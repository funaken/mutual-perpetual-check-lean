import MPC.Glare.TraceGlare
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.TraceGlare

History-based immovability versus constant contents, a glare blocked on the
actual board, Lemma 2.4 for a king that leaves its rook's file, and a glaring
drop. Board updates here make no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Trace glare verification must not import GameSeq"

namespace MPC
namespace TraceGlareTests

/-! ## Constant contents are not immovability -/

private def goldState : BoardState :=
  { board :=
    { grid := fun q => if q = (4, 4) then some ⟨.sente, .gold⟩ else none
      hand := fun _ => ∅ }
    turn := .sente }
-- Dropping an identical gold onto its own square: a board update only.
private def touched : MoveTrace := MoveTrace.single goldState (.dropMove .gold (4, 4))

-- The contents of (4, 4) never change, yet the square is a drop destination, so
-- the initial gold is not immovable in the history sense.
example :
    (∀ k : Fin 2, (touched.states k).board.grid (4, 4) = (touched.states 0).board.grid (4, 4)) ∧
    ¬ touched.ImmovableAt (4, 4) := by
  decide

/-! ## Lemma 2.4: a king leaves its own rook's file -/

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

private theorem king_no_glare (p : Player) (b : Board) (target : Pos)
    (h : Pos.dirTo (5, 4) target ∉ PieceType.king.stepDirs.map (Dir.forPlayer · p)) :
    ¬ attacksOriented b p .king (5, 4) target := by
  rintro (hs | ⟨_, hsd, _⟩)
  · exact h hs
  · simp [PieceType.slideDirs] at hsd

private def premisesOf (p : Player) : Prop :=
  let tr := MoveTrace.single (initial p) (unblock p)
  let kp := tr.kingPositionsFrom (positions p)
  tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧ tr.KingsWellPlaced kp ∧
    tr.EveryMoveLeavesOwnKingSafe kp ∧ tr.InitialOpponentKingSafe kp ∧ tr.EveryMoveChecksOpponent kp

private theorem premises (p : Player) : premisesOf p := by
  dsimp only [premisesOf]
  let tr := MoveTrace.single (initial p) (unblock p)
  have ht := MoveTrace.single_followsTransitions (initial p) (unblock p)
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (col p 2) (5, 4) false = .boardMove src dst pr at hm
    cases hm
    exact ⟨⟨p, .king⟩, by cases p <;> rfl, rfl⟩
  · apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions p) ht
    · intro i o; have hi := Fin.eq_zero i; subst i
      change (initial p).board.grid (5, 4) ≠ some ⟨o, .king⟩
      cases p <;> cases o <;> decide
    · intro i pt dst hm; change Move.boardMove _ _ _ = .dropMove pt dst at hm; cases hm
    · exact placed p
  · intro i; have hi := Fin.eq_zero i; subst i
    cases p
    exacts [after_safe .sente, after_safe .gote]
  · cases p
    exacts [start_safe .sente, start_safe .gote]
  · intro i; have hi := Fin.eq_zero i; subst i
    cases p
    exacts [rook_check .sente, rook_check .gote]

-- Both owners. The rook and the enemy king are immovable, the moving king is not.
-- Initially the rook is blocked by its own king but already glares, because the
-- king is removed from the stripped board. The moved king does not glare, so the
-- trace theorem yields an unblocked checker: Lemma 2.4.
example (p : Player) :
    let tr := MoveTrace.single (initial p) (unblock p)
    let kp := tr.kingPositionsFrom (positions p)
    tr.ImmovableAt (col p 0) ∧ tr.ImmovableAt (col p 4) ∧ ¬ tr.ImmovableAt (col p 2) ∧
    ¬ attacksOriented (tr.states 0).board p .rook (col p 0) (col p 4) ∧
    tr.GlaresAtEnemyKing kp 0 (col p 0) ∧
    ¬ tr.GlaresAtEnemyKing kp 1 (5, 4) ∧
    hasUnblockedCheckerOriented (tr.before (0 : Fin 1)).board (tr.after (0 : Fin 1)).board
      (tr.moves (0 : Fin 1)) p.opponent (kp 1 p.opponent) := by
  dsimp only
  obtain ⟨ht, hs, hk, hsafe, h0, hc⟩ := premises p
  have hng : ¬ (MoveTrace.single (initial p) (unblock p)).GlaresAtEnemyKing
      ((MoveTrace.single (initial p) (unblock p)).kingPositionsFrom (positions p)) 1 (5, 4) := by
    rintro ⟨piece, hp, ha⟩
    change (applyMove (initial p) (unblock p)).board.grid (5, 4) = some piece at hp
    rw [after_grid, ite_eq_left rfl] at hp
    cases hp
    exact king_no_glare p _ _ (by cases p <;> decide) ha
  refine ⟨by cases p <;> decide, by cases p <;> decide, by cases p <;> decide, ?_, ?_, hng, ?_⟩
  · intro ha
    have h := ((col_clear _ p).mp ((col_attack _ p).mp ha)).2.1
    revert h
    cases p <;> decide
  · refine ⟨⟨p, .rook⟩, by cases p <;> rfl, ?_⟩
    cases p
    · exact (col_attack _ .sente).mpr ((col_clear _ .sente).mpr ⟨by decide, by decide, by decide⟩)
    · exact (col_attack _ .gote).mpr ((col_clear _ .gote).mpr ⟨by decide, by decide, by decide⟩)
  · exact ((MoveTrace.single (initial p) (unblock p)).everyMoveChecksOpponent_glares_or_unblocked
      _ ht hs hk hsafe h0 hc (0 : Fin 1)).resolve_left hng

/-! ## Every drop glares -/

private def beside (p : Player) : Pos := (1, if p = .sente then 4 else 0)
private def dropGold (p : Player) : Move := .dropMove .gold (beside p)

private theorem drop_grid (p : Player) (q : Pos) :
    (applyMove (initial p) (dropGold p)).board.grid q =
      if q = beside p then some ⟨p, .gold⟩ else (initial p).board.grid q := by
  by_cases hb : q = beside p
  · subst q; rw [ite_eq_left rfl]
    exact applyMove_dropMove_grid_dst (initial p) .gold (beside p)
  · rw [ite_eq_right hb]
    exact applyMove_dropMove_grid_other (initial p) .gold (beside p) q hb

private theorem drop_safe (p : Player) :
    ¬ inCheckOriented (applyMove (initial p) (dropGold p)).board p (col p 2) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [drop_grid] at hp
  dsimp only [initial] at hp
  split_ifs at hp
  · cases hp; cases p <;> cases ho
  · cases hp; cases p <;> cases ho
  · cases hp; cases p <;> cases ho
  · cases hp; subst pos
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs; cases p <;> decide
    · simp [PieceType.slideDirs] at hsd

private theorem drop_check (p : Player) :
    hasDestinationCheckerOriented (applyMove (initial p) (dropGold p)).board (dropGold p)
      p.opponent (col p 4) := by
  refine ⟨⟨p, .gold⟩, applyMove_dropMove_grid_dst (initial p) .gold (beside p), ?_, ?_⟩
  · cases p <;> rfl
  · cases p <;> left <;> decide

-- Both owners: a gold dropped beside the enemy king, applied through the trace
-- theorem that every drop in a mutual-check trace glares.
example (p : Player) :
    let tr := MoveTrace.single (initial p) (dropGold p)
    tr.GlaresAtEnemyKing (tr.kingPositionsFrom (positions p)) 1 (beside p) := by
  dsimp only
  let tr := MoveTrace.single (initial p) (dropGold p)
  have ht := MoveTrace.single_followsTransitions (initial p) (dropGold p)
  have hs : tr.BoardMoveSourcesOwned := by
    intro i src dst pr hm
    change Move.dropMove .gold (beside p) = .boardMove src dst pr at hm
    cases hm
  have hk : tr.KingsWellPlaced (tr.kingPositionsFrom (positions p)) := by
    apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions p) ht
    · intro i o; have hi := Fin.eq_zero i; subst i
      change (initial p).board.grid (beside p) ≠ some ⟨o, .king⟩
      cases p <;> cases o <;> decide
    · intro i pt dst hm
      change Move.dropMove .gold (beside p) = .dropMove pt dst at hm
      cases hm; decide
    · exact placed p
  have hsafe : tr.EveryMoveLeavesOwnKingSafe (tr.kingPositionsFrom (positions p)) := by
    intro i; have hi := Fin.eq_zero i; subst i
    cases p
    exacts [drop_safe .sente, drop_safe .gote]
  have h0 : tr.InitialOpponentKingSafe (tr.kingPositionsFrom (positions p)) := by
    cases p
    exacts [start_safe .sente, start_safe .gote]
  have hc : tr.EveryMoveChecksOpponent (tr.kingPositionsFrom (positions p)) := by
    intro i; have hi := Fin.eq_zero i; subst i
    cases p
    exacts [inCheckOriented_of_destinationChecker _ _ _ _ (drop_check .sente),
      inCheckOriented_of_destinationChecker _ _ _ _ (drop_check .gote)]
  exact tr.dropMove_glares_of_everyMoveChecksOpponent _ ht hs hk hsafe h0 hc (0 : Fin 1) .gold (beside p) rfl

end TraceGlareTests
end MPC
