import MPC.Legacy.MoveCompatibility
import MPC.Legacy.MoveTrace
import MPC.Legacy.CheckCompatibility
import MPC.Legacy.CheckOrigin
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.LegacyCheckOrigin

A compatible discovered-check trace classified through the legacy predicates, and
concrete disagreements between legacy and oriented checks for gote's gold and
sente's lance. Board updates here make no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Legacy check origin verification must not import GameSeq"

namespace MPC
namespace LegacyCheckOriginTests

/-! ## A compatible discovered check, classified by the legacy predicates -/

private def col (p : Player) (j : Fin 9) : Pos := (0, if p = .sente then j else 4 - j)
-- The mover's king blocks its own rook; moving the king off the file opens the line.
private def initial (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = col p 0 then some ⟨p, .rook⟩
        else if q = col p 2 then some ⟨p, .king⟩
        else if q = col p 4 then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
private def unblock (p : Player) : Move := .boardMove (col p 2) (5, 4) false
private def positions (p : Player) : Player → Pos := fun o => if o = p then col p 2 else col p 4

private theorem col_clear (b : Board) (p : Player) :
    pathClear b (col p 0) (col p 4) ↔
      b.grid (col p 1) = none ∧ b.grid (col p 2) = none ∧ b.grid (col p 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (col p 0) (col p 4)
    (0, if p = .sente then 1 else -1) 4 (by cases p <;> decide) (by decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h3 := hc.mp h 3 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    cases p <;> exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j <;> cases p <;> assumption

private theorem col_attack (b : Board) (p : Player) :
    attacksOriented b p .rook (col p 0) (col p 4) ↔ pathClear b (col p 0) (col p 4) := by
  constructor
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · simp [PieceType.stepDirs] at hs
    · exact hc
  · intro hc
    refine Or.inr ⟨(0, if p = .sente then 1 else -1), ?_, ?_, 4, by decide, ?_, ?_, hc⟩ <;>
      cases p <;> decide

private theorem after_grid (p : Player) (q : Pos) :
    (applyMove (initial p) (unblock p)).board.grid q =
      if q = (5, 4) then some ⟨p, .king⟩
      else if q = col p 2 then none else (initial p).board.grid q := by
  by_cases hd : q = (5, 4)
  · subst q; rw [ite_eq_left rfl]; cases p <;> rfl
  · by_cases hs : q = col p 2
    · subst q; rw [ite_eq_right hd, ite_eq_left rfl]; cases p <;> rfl
    · rw [ite_eq_right hd, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (initial p) (col p 2) (5, 4) false q hs hd

private theorem placed (p : Player) : KingsWellPlaced (initial p).board (positions p) := by
  intro o q
  cases p <;> cases o <;> by_cases h1 : q = (0, 0) <;> by_cases h2 : q = (0, 2) <;>
    by_cases h3 : q = (0, 4) <;> simp_all [initial, positions, col, Player.opponent]

-- Initially the rook is blocked by the mover's own king, which is too far to check.
private theorem start_safe (p : Player) :
    ¬ inCheckOriented (initial p).board p.opponent (col p 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [initial] at hp
  split_ifs at hp
  · cases hp; subst pos
    have h := ((col_clear _ p).mp ((col_attack _ p).mp ha)).2.1
    cases p <;> simp [initial, col] at h
  · cases hp; subst pos
    cases p
    · simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
        PieceType.slideDirs, col, Pos.dirTo, Dir.forPlayer] at ha
    · simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
        PieceType.slideDirs, col, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha
  · cases hp; cases p <;> cases ho

private theorem after_safe (p : Player) :
    ¬ inCheckOriented (applyMove (initial p) (unblock p)).board p (5, 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [after_grid] at hp
  dsimp only [initial] at hp
  split_ifs at hp
  · cases hp; cases p <;> cases ho
  · cases hp; cases p <;> cases ho
  · cases hp; subst pos
    cases p <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
      PieceType.slideDirs, col, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha <;> revert ha <;> decide

private theorem rook_check (p : Player) :
    inCheckOriented (applyMove (initial p) (unblock p)).board p.opponent (col p 4) :=
  ⟨col p 0, ⟨p, .rook⟩, by cases p <;> rfl, by cases p <;> rfl,
    (col_attack _ p).mpr ((col_clear _ p).mpr (by cases p <;> exact ⟨rfl, rfl, rfl⟩))⟩

private theorem no_legacy_direct (p : Player) :
    ¬ isDirectCheck (applyMove (initial p) (unblock p)).board (unblock p) (col p 4) := by
  rintro ⟨piece, hp, ha⟩
  rw [after_grid, ite_eq_left rfl] at hp
  cases hp
  cases p <;> simp [attacks, canMoveTo, PieceType.stepDirs, PieceType.slideDirs, col,
    Pos.dirTo, Dir.forPlayer, Dir.flip, Player.opponent] at ha

private theorem after_compatible (p : Player) (pos : Pos) (piece : Piece)
    (hp : (applyMove (initial p) (unblock p)).board.grid pos = some piece)
    (ho : piece.owner = p) : piece.pieceType.LegacyCompatible piece.owner := by
  rw [after_grid] at hp
  dsimp only [initial] at hp
  split_ifs at hp
  · cases hp; exact Or.inl rfl
  · cases hp; exact Or.inr (Or.inl rfl)
  · cases hp; cases p <;> cases ho

-- Both owners: the mover's king steps off its rook's file. the stated transition and safety premises and
-- legacy compatibility hold, so the legacy disjunction applies; the moved king does
-- not check, hence the move is a legacy discovered check.
example (p : Player) :
    let tr := MoveTrace.single (initial p) (unblock p)
    let kp := tr.kingPositionsFrom (positions p)
    tr.EveryMoveChecksOpponent kp ∧
    ¬ isDirectCheck (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1)) (kp 1 p.opponent) ∧
    isDiscoveredCheck (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1)) p (kp 1 p.opponent) := by
  dsimp only
  let tr := MoveTrace.single (initial p) (unblock p)
  have ht := MoveTrace.single_followsTransitions (initial p) (unblock p)
  have hs : tr.BoardMoveSourcesOwned := by
    intro i src dst pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (col p 2) (5, 4) false = .boardMove src dst pr at hm
    cases hm
    exact ⟨⟨p, .king⟩, by cases p <;> rfl, rfl⟩
  have hk : tr.KingsWellPlaced (tr.kingPositionsFrom (positions p)) := by
    apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions p) ht
    · intro i o; have hi := Fin.eq_zero i; subst i
      change (initial p).board.grid (5, 4) ≠ some ⟨o, .king⟩
      cases p <;> cases o <;> decide
    · intro i pt dst hm; change Move.boardMove _ _ _ = .dropMove pt dst at hm; cases hm
    · exact placed p
  have hsafe : tr.EveryMoveLeavesOwnKingSafe (tr.kingPositionsFrom (positions p)) := by
    intro i; have hi := Fin.eq_zero i; subst i
    cases p
    exacts [after_safe .sente, after_safe .gote]
  have h0 : tr.InitialOpponentKingSafe (tr.kingPositionsFrom (positions p)) := by
    cases p
    exacts [start_safe .sente, start_safe .gote]
  have hc : tr.MoverPiecesLegacyCompatible := by
    intro i pos piece hp ho; have hi := Fin.eq_zero i; subst i
    exact after_compatible p pos piece hp ho
  have hcheck : tr.EveryMoveChecksOpponent (tr.kingPositionsFrom (positions p)) := by
    intro i; have hi := Fin.eq_zero i; subst i
    cases p
    exacts [rook_check .sente, rook_check .gote]
  have hleg := (tr.everyMoveChecksOpponent_iff_legacy_direct_or_discovered _ ht hs hk hsafe h0
    hc).mp hcheck
  refine ⟨hcheck, ?_, ?_⟩
  · cases p
    exacts [no_legacy_direct .sente, no_legacy_direct .gote]
  · cases p
    exacts [(hleg (0 : Fin 1)).resolve_left (no_legacy_direct .sente),
      (hleg (0 : Fin 1)).resolve_left (no_legacy_direct .gote)]

/-! ## Disagreements outside compatibility -/

-- Only the target king, opposing the player to move.
private def lone (t : Player) : BoardState :=
  { board :=
    { grid := fun q => if q = (4, 4) then some ⟨t.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := t }

-- Missed by legacy: a gote gold dropped diagonally in front (gote's forward is -y)
-- checks the sente king, but the legacy step test uses sente's gold table.
example :
    hasDestinationCheckerOriented (applyMove (lone .gote) (.dropMove .gold (3, 5))).board
      (.dropMove .gold (3, 5)) .sente (4, 4) ∧
    ¬ isDirectCheck (applyMove (lone .gote) (.dropMove .gold (3, 5))).board
      (.dropMove .gold (3, 5)) (4, 4) := by
  refine ⟨⟨⟨.gote, .gold⟩, applyMove_dropMove_grid_dst _ _ _, rfl, by left; decide⟩, ?_⟩
  rintro ⟨o, h | ⟨_, hsd, _⟩⟩
  · revert h; cases o <;> decide
  · simp [PieceType.slideDirs] at hsd

-- False positive in legacy: a gote gold dropped diagonally behind is reported as a
-- direct check, although gote's gold cannot move diagonally backwards.
example :
    isDirectCheck (applyMove (lone .gote) (.dropMove .gold (3, 3))).board
      (.dropMove .gold (3, 3)) (4, 4) ∧
    ¬ hasDestinationCheckerOriented (applyMove (lone .gote) (.dropMove .gold (3, 3))).board
      (.dropMove .gold (3, 3)) .sente (4, 4) := by
  refine ⟨⟨.gote, Or.inl (by decide)⟩, ?_⟩
  rintro ⟨piece, hp, _, ha⟩
  change (applyMove (lone .gote) (.dropMove .gold (3, 3))).board.grid (3, 3) = some piece at hp
  rw [applyMove_dropMove_grid_dst] at hp
  cases hp
  rcases ha with h | ⟨_, hsd, _⟩
  · revert h; decide
  · simp [PieceType.slideDirs] at hsd

private def lanceBoard : Board :=
  { grid := fun q =>
      if q = (4, 0) then some ⟨.sente, .lance⟩ else if q = (4, 4) then some ⟨.gote, .king⟩ else none
    hand := fun _ => ∅ }

-- Missed by legacy: sente's lance attacks forward along a clear file, but the legacy
-- slide test uses the opponent's (reversed) lance direction.
example :
    attacksOriented lanceBoard .sente .lance (4, 0) (4, 4) ∧
    ¬ attacks lanceBoard .sente .lance (4, 0) (4, 4) := by
  constructor
  · refine Or.inr ⟨(0, 1), by decide, by decide, 4, by decide, by decide, by decide, ?_⟩
    apply (pathClear_iff_of_exact_steps lanceBoard (4, 0) (4, 4) (0, 1) 4 (by decide) (by decide)
      (by decide) (by decide) (by decide)).mpr
    intro j hj hjn hob
    interval_cases j <;> rfl
  · rintro (h | ⟨sd, hsd, hn, _⟩)
    · simp [PieceType.stepDirs] at h
    · simp [PieceType.slideDirs, Dir.forPlayer, Dir.flip, Player.opponent] at hsd
      subst hsd
      revert hn
      decide

-- Drops never have a legacy discovered check or an unblocked checker.
example (before after : Board) (pt : PieceType) (dst target : Pos) (player : Player) :
    isDiscoveredCheck after (.dropMove pt dst) player target ↔
      hasUnblockedCheckerOriented before after (.dropMove pt dst) player.opponent target :=
  Iff.rfl

end LegacyCheckOriginTests
end MPC
