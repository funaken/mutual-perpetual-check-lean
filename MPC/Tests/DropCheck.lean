import MPC.Legacy.CheckCompatibility
import MPC.Trace.DropCheck
import MPC.Basic.SlidePath
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.DropCheck

Drop-check origin, backwards-only preservation, and generated king positions.
Occupied destinations and empty hands deliberately make no full-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Drop check verification must not import GameSeq"

namespace MPC.DropCheckTests

private def landing : Player → Pos
  | .sente => (4, 3)
  | .gote => (4, 5)
private def positions (turn : Player) : Player → Pos :=
  fun p => if p = turn then (0, 0) else (4, 4)
private def initial (turn : Player) (occupied : Bool) : BoardState :=
  { board :=
    { grid := fun q => if q = (0, 0) then some ⟨turn, .king⟩
        else if q = (4, 4) then some ⟨turn.opponent, .king⟩
        else if q = landing turn ∧ occupied = true then some ⟨turn.opponent, .pawn⟩ else none
      hand := fun _ => ∅ }
    turn := turn }

private theorem before_safe (turn : Player) (occupied : Bool) :
    ¬ inCheckOriented (initial turn occupied).board turn.opponent (4, 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [initial] at hp
  split_ifs at hp with h0 h4 hd
  · cases hp; subst pos
    cases turn <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
      PieceType.slideDirs, Dir.forPlayer, Dir.flip, Pos.dirTo] at ha
  · cases hp; cases turn <;> cases ho
  · cases hp; cases turn <;> cases ho

private theorem placed (turn : Player) (occupied : Bool) :
    KingsWellPlaced (initial turn occupied).board (positions turn) := by
  intro p q
  cases turn <;> cases p <;> cases occupied <;> by_cases h0 : q = (0, 0) <;>
    by_cases h4 : q = (4, 4) <;> by_cases h3 : q = (4, 3) <;> by_cases h5 : q = (4, 5) <;>
    simp_all [initial, positions, landing, Player.opponent]

private theorem destination_checker (turn : Player) (occupied : Bool) :
    hasDestinationCheckerOriented (applyMove (initial turn occupied) (.dropMove .pawn (landing turn))).board
      (.dropMove .pawn (landing turn)) turn.opponent (4, 4) := by
  refine ⟨⟨turn, .pawn⟩, applyMove_dropMove_grid_dst _ _ _, ?_, ?_⟩
  · cases turn <;> rfl
  · cases turn <;> left <;> decide

-- Both turns and both destination occupancies: derive actual king placement,
-- apply the trace equivalence, and exclude other checkers using before-non-check.
example (turn : Player) (occupied : Bool) :
    let tr := MoveTrace.single (initial turn occupied) (.dropMove .pawn (landing turn))
    let kp := tr.kingPositionsFrom (positions turn)
    tr.KingsWellPlaced kp ∧
    inCheckOriented (tr.after (0 : Fin 1)).board turn.opponent (kp 1 turn.opponent) ∧
    hasDestinationCheckerOriented (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1))
      turn.opponent (kp 1 turn.opponent) ∧
    ¬ hasOtherCheckerOriented (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1))
      turn.opponent (kp 1 turn.opponent) := by
  dsimp only
  let tr := MoveTrace.single (initial turn occupied) (.dropMove .pawn (landing turn))
  have ht := MoveTrace.single_followsTransitions (initial turn occupied) (.dropMove .pawn (landing turn))
  have hp : tr.KingsWellPlaced (tr.kingPositionsFrom (positions turn)) := by
    apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions turn) ht
    · intro i p; have hi := Fin.eq_zero i; subst i
      change (initial turn occupied).board.grid (landing turn) ≠ some ⟨p, .king⟩
      cases turn <;> cases occupied <;> cases p <;> decide
    · intro i pt dst hm
      change Move.dropMove .pawn (landing turn) = .dropMove pt dst at hm
      cases hm; decide
    · exact placed turn occupied
  have hk : tr.kingPositionsFrom (positions turn) (Fin.succ (0 : Fin 1)) turn.opponent = (4, 4) := by
    cases turn <;> rfl
  have he := MoveTrace.dropMove_inCheck_iff_destinationChecker tr ht
    (tr.kingPositionsFrom (positions turn)) (0 : Fin 1) .pawn (landing turn) turn.opponent rfl
    (by cases turn <;> rfl) (by cases turn <;> exact before_safe _ occupied)
  rw [hk] at he
  have hd := destination_checker turn occupied
  have hn := applyMove_dropMove_not_otherChecker_of_not_inCheck (initial turn occupied)
    .pawn (landing turn) (4, 4) turn.opponent (before_safe turn occupied)
  refine ⟨hp, ?_⟩
  cases turn <;> exact ⟨he.mpr hd, hd, hn⟩

private def rayPoint (diagonal : Bool) (j : Fin 9) : Pos := if diagonal then (j, j) else (j, 0)
private def rayDir (diagonal : Bool) : Dir := if diagonal then (1, 1) else (1, 0)
private def rayKind (diagonal : Bool) : PieceType := if diagonal then .bishop else .rook
private def rayState (turn : Player) (diagonal : Bool) : BoardState :=
  { board := { grid := fun p => if p = (0, 0) then some ⟨turn, rayKind diagonal⟩ else none
               hand := fun _ => ∅ }
    turn := turn }

-- The slide-path specification identifies the two actual interior squares, so a new blocker at the
-- first one destroys the old ray even though attacks always transfer backwards.
private theorem ray_clear (b : Board) (diagonal : Bool) :
    pathClear b (0, 0) (rayPoint diagonal 3) ↔
      b.grid (rayPoint diagonal 1) = none ∧ b.grid (rayPoint diagonal 2) = none := by
  have hc := pathClear_iff_of_exact_steps b (0, 0) (rayPoint diagonal 3) (rayDir diagonal) 3
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
    interval_cases j <;> cases diagonal <;> assumption

example (turn : Player) (diagonal : Bool) :
    let bs := rayState turn diagonal
    attacksOriented bs.board turn (rayKind diagonal) (0, 0) (rayPoint diagonal 3) ∧
    ¬ attacksOriented (applyMove bs (.dropMove .gold (rayPoint diagonal 1))).board
      turn (rayKind diagonal) (0, 0) (rayPoint diagonal 3) := by
  constructor
  · refine Or.inr ⟨rayDir diagonal, ?_, ?_, 3, by decide, ?_, ?_, ?_⟩
    · cases turn <;> cases diagonal <;> decide
    · cases diagonal <;> decide
    · cases diagonal <;> decide
    · cases diagonal <;> decide
    · apply (ray_clear _ diagonal).mpr
      cases diagonal <;> exact ⟨rfl, rfl⟩
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · cases diagonal <;> simp [rayKind, PieceType.stepDirs] at hs
    · have he := ((ray_clear _ diagonal).mp hc).1
      rw [applyMove_dropMove_grid_dst] at he
      cases he

private def continuing (turn : Player) : BoardState :=
  { board := { grid := fun p => if p = (5, 4) then some ⟨turn, .gold⟩ else none
               hand := fun _ => ∅ }
    turn := turn }

-- The target is empty here. Existing other check and newly dropped destination
-- check coexist: the before-non-check premise cannot be omitted.
example (turn : Player) :
    let bs := continuing turn
    let after := applyMove bs (.dropMove .gold (3, 4))
    bs.board.grid (4, 4) = none ∧ inCheckOriented bs.board turn.opponent (4, 4) ∧
    hasOtherCheckerOriented after.board (.dropMove .gold (3, 4)) turn.opponent (4, 4) ∧
    hasDestinationCheckerOriented after.board (.dropMove .gold (3, 4)) turn.opponent (4, 4) := by
  have ho : hasOtherCheckerOriented (applyMove (continuing turn) (.dropMove .gold (3, 4))).board
      (.dropMove .gold (3, 4)) turn.opponent (4, 4) := by
    refine ⟨(5, 4), by decide, ⟨turn, .gold⟩, rfl, ?_, ?_⟩
    · cases turn <;> rfl
    · cases turn <;> left <;> decide
  refine ⟨rfl, inCheckOriented_of_otherChecker _ _ _ _
    (applyMove_dropMove_otherChecker_before _ _ _ _ _ ho), ho, ⟨⟨turn, .gold⟩, rfl, ?_, ?_⟩⟩
  · cases turn <;> rfl
  · cases turn <;> left <;> decide

end MPC.DropCheckTests
