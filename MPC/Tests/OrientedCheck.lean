import MPC.Legacy.MoveCompatibility
import MPC.Legacy.MoveTrace
import MPC.Legacy.CheckCompatibility
import MPC.Basic.OrientedCheck
import MPC.Basic.SlidePath
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.OrientedCheck

Direction, occupancy, and preservation checks . A supplied
target position need not contain a king; full legality is not asserted.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Oriented check verification must not import GameSeq"

namespace MPC

private def singleChecker (owner : Player) (pt : PieceType) (src : Pos) : Board :=
  { grid := fun p => if p = src then some ⟨owner, pt⟩ else none, hand := fun _ => ∅ }

private theorem single_grid (owner : Player) (pt : PieceType) (src pos : Pos) (p : Piece) :
    (singleChecker owner pt src).grid pos = some p ↔ pos = src ∧ p = ⟨owner, pt⟩ := by
  by_cases h : pos = src
  · subst pos; simp [singleChecker, eq_comm]
  · simp [singleChecker, h]

private theorem single_check (owner player : Player) (pt : PieceType) (src dst : Pos) :
    inCheckOriented (singleChecker owner pt src) player dst ↔
      owner = player.opponent ∧
      attacksOriented (singleChecker owner pt src) owner pt src dst := by
  constructor
  · rintro ⟨pos, piece, hp, ho, ha⟩
    obtain ⟨rfl, rfl⟩ := (single_grid _ _ _ _ _).mp hp
    exact ⟨ho, ha⟩
  · rintro ⟨ho, ha⟩
    exact ⟨src, ⟨owner, pt⟩, by simp [singleChecker], ho, ha⟩

private theorem single_legacy_check (owner player : Player) (pt : PieceType) (src dst : Pos) :
    inCheck (singleChecker owner pt src) player dst ↔
      owner = player.opponent ∧ attacks (singleChecker owner pt src) owner pt src dst := by
  constructor
  · rintro ⟨pos, piece, hp, ho, ha⟩
    obtain ⟨rfl, rfl⟩ := (single_grid _ _ _ _ _).mp hp
    exact ⟨ho, ha⟩
  · rintro ⟨ho, ha⟩
    exact ⟨src, ⟨owner, pt⟩, by simp [singleChecker], ho, ha⟩

private def forward (owner : Player) : Pos :=
  match owner with | .sente => (4, 5) | .gote => (4, 3)

-- Both owners' pawns/lances check forward even when the target square is empty.
example (owner : Player) (pt : PieceType) (hpt : pt = .pawn ∨ pt = .lance) :
    inCheckOriented (singleChecker owner pt (4, 4)) owner.opponent (forward owner) ∧
      (singleChecker owner pt (4, 4)).grid (forward owner) = none := by
  constructor
  · apply (single_check _ _ _ _ _).mpr
    refine ⟨by cases owner <;> rfl, ?_⟩
    rcases hpt with rfl | rfl
    · cases owner <;> left <;> decide
    · cases owner
      · exact Or.inr ⟨(0, 1), by decide, by decide, 1, by decide, by decide, by decide,
          by simp [pathClear, forward, show slidePath (4, 4) (4, 5) = [] from by decide]⟩
      · exact Or.inr ⟨(0, -1), by decide, by decide, 1, by decide, by decide, by decide,
          by simp [pathClear, forward, show slidePath (4, 4) (4, 3) = [] from by decide]⟩
  · cases owner <;> rfl

example (owner : Player) (pt : PieceType) (hpt : pt = .pawn ∨ pt = .lance) :
    ¬ inCheckOriented (singleChecker owner pt (4, 4)) owner.opponent (forward owner.opponent) := by
  rw [single_check]
  rcases hpt with rfl | rfl <;> cases owner <;>
    simp [attacksOriented, canMoveToOriented, forward, Player.opponent,
      PieceType.stepDirs, PieceType.slideDirs, Dir.forPlayer, Dir.flip, Dir.normalize,
      show Pos.dirTo (4, 4) (4, 3) = (0, -1) from by decide,
      show Pos.dirTo (4, 4) (4, 5) = (0, 1) from by decide]

-- Legacy pawn steps ignore the owner; legacy lance slides reverse forward motion.
example : ¬ inCheck (singleChecker .gote .pawn (4, 4)) .sente (4, 3) ∧
    ¬ inCheck (singleChecker .sente .lance (4, 4)) .gote (4, 5) := by
  constructor <;> rw [single_legacy_check] <;>
    simp [attacks, canMoveTo, PieceType.stepDirs, PieceType.slideDirs,
      Player.opponent, Dir.forPlayer, Dir.flip, Dir.normalize,
      show Pos.dirTo (4, 4) (4, 3) = (0, -1) from by decide,
      show Pos.dirTo (4, 4) (4, 5) = (0, 1) from by decide]

-- Geometric attack alone does not supply a present checker. Removing the sole
-- checker preserves all empty squares but leaves no check witness.
example (owner : Player) (target : Pos) :
    attacksOriented { grid := fun _ => none, hand := fun _ => ∅ }
      owner .pawn (4, 4) (forward owner) ∧
    ¬ inCheckOriented { grid := fun _ => none, hand := fun _ => ∅ } owner target := by
  constructor
  · cases owner <;> left <;> decide
  · simp [inCheckOriented]

example (owner : Player) :
    ¬ inCheckOriented ((singleChecker owner .pawn (4, 4)).setGrid (4, 4) none)
      owner.opponent (forward owner) := by
  rintro ⟨pos, piece, hp, _⟩
  by_cases h : pos = (4, 4) <;> simp [Board.setGrid, singleChecker, h] at hp

example (board : Board) (player : Player) (target : Pos)
    (h : ∀ pos piece, board.grid pos = some piece → piece.owner = player) :
    ¬ inCheckOriented board player target := by
  rintro ⟨pos, piece, hp, ho, _⟩
  have heq := (h pos piece hp).symm.trans ho
  cases player <;> cases heq

private def rayTarget (diagonal : Bool) : Pos := if diagonal then (3, 3) else (3, 0)
private def rayDir (diagonal : Bool) : Dir := if diagonal then (1, 1) else (1, 0)
private def rayPoint (diagonal : Bool) (j : Fin 9) : Pos := if diagonal then (j, j) else (j, 0)

-- The slide-path specification supplies the clearance specification for both a rook and a bishop ray.
private theorem ray_clear (board : Board) (diagonal : Bool) :
    pathClear board (0, 0) (rayTarget diagonal) ↔
      board.grid (rayPoint diagonal 1) = none ∧ board.grid (rayPoint diagonal 2) = none := by
  have hc := pathClear_iff_of_exact_steps board (0, 0) (rayTarget diagonal) (rayDir diagonal) 3
    (by cases diagonal <;> decide) (by decide) (by cases diagonal <;> decide)
    (by cases diagonal <;> decide) (by cases diagonal <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases diagonal <;> unfold onBoard <;> decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by cases diagonal <;> unfold onBoard <;> decide)
    cases diagonal <;> exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j <;> cases diagonal
    · exact h1
    · exact h1
    · exact h2
    · exact h2

example (owner : Player) (diagonal : Bool) :
    inCheckOriented (singleChecker owner (if diagonal then .bishop else .rook) (0, 0))
      owner.opponent (rayTarget diagonal) := by
  apply (single_check _ _ _ _ _).mpr
  refine ⟨by cases owner <;> rfl, Or.inr ⟨rayDir diagonal, ?_, ?_, 3, by decide, ?_, ?_, ?_⟩⟩
  · cases diagonal <;> cases owner <;> decide
  · cases diagonal <;> decide
  · cases diagonal <;> decide
  · cases diagonal <;> decide
  · apply (ray_clear _ diagonal).mpr
    cases diagonal <;> exact ⟨rfl, rfl⟩

example (board : Board) (owner : Player) (diagonal : Bool) (blocker : Piece)
    (hb : board.grid (rayPoint diagonal 1) = some blocker) :
    ¬ attacksOriented board owner (if diagonal then .bishop else .rook) (0, 0) (rayTarget diagonal) := by
  rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
  · cases diagonal <;> simp [PieceType.stepDirs] at hs
  · have he := ((ray_clear board diagonal).mp hc).1
    rw [hb] at he
    cases he

example (board : Board) (diagonal : Bool) (h2 : board.grid (rayPoint diagonal 2) = none) :
    pathClear (board.setGrid (rayPoint diagonal 1) none) (0, 0) (rayTarget diagonal) := by
  apply (ray_clear _ diagonal).mpr
  have hne : rayPoint diagonal 2 ≠ rayPoint diagonal 1 := by cases diagonal <;> decide
  simp [Board.setGrid, hne, h2]

-- Removing a non-checking piece preserves an existing check. No assertion about
-- a global immovable class or about legality of the board update is needed.
example (board : Board) (player : Player) (target removed : Pos)
    (hc : inCheckOriented board player target)
    (hn : ∀ piece, board.grid removed = some piece → piece.owner = player.opponent →
      ¬ attacksOriented board piece.owner piece.pieceType removed target) :
    inCheckOriented (board.setGrid removed none) player target := by
  apply inCheckOriented_mono_of_checkers_preserved board _ player target ?_ ?_ hc
  · intro q hq
    by_cases h : q = removed <;> simp [Board.setGrid, h, hq]
  · intro pos piece hp ho ha
    have hne : pos ≠ removed := by intro heq; subst pos; exact hn piece hp ho ha
    simp [Board.setGrid, hne, hp]

example (board : Board) (owner : Player) (pt : PieceType) (pos : Pos) :
    ¬ attacksOriented board owner pt pos pos := attacksOriented_not_self board owner pt pos

example (board : Board) (player : Player) (target : Pos)
    (hs : ∀ pos piece, board.grid pos = some piece → piece.owner = player.opponent →
      piece.pieceType = .king ∨ piece.pieceType = .rook ∨ piece.pieceType = .bishop ∨
      piece.pieceType = .dragon ∨ piece.pieceType = .horse) :
    inCheckOriented board player target ↔ inCheck board player target :=
  inCheckOriented_iff_inCheck_of_symmetric board player target hs

example (board : Board) (hand : Player → Hand) (player : Player) (target : Pos) :
    inCheckOriented { board with hand := hand } player target ↔ inCheckOriented board player target :=
  Iff.rfl

end MPC
