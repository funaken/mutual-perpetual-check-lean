import MPC.Trace.MutualCheck
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.MainTrace

The skeleton's king step needs periodicity. For both first movers, a one-move trace satisfies 's
premises, mutual check, and the movement condition. Its move is a discovered check
that moves the non-glaring king (`OpenableMoveBy … .king`), and the trace is not
periodic. So `not_openableMove_king` cannot drop periodicity. The same trace has at
most two bishop/horse squares and at most two rook/dragon squares in every state
(`PieceCountsAtMostTwo`). The board updates make no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Main trace verification must not import GameSeq"

namespace MPC
namespace MainTraceTests

private def col (p : Player) (j : Fin 9) : Pos := (0, if p = .sente then j else 4 - j)
-- The mover's king blocks its own rook on the file of the enemy king.
private def initial (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = col p 0 then some ⟨p, .rook⟩
        else if q = col p 2 then some ⟨p, .king⟩
        else if q = col p 4 then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
private def kingMove (p : Player) (dst : Pos) : Move := .boardMove (col p 2) dst false
private def positions (p : Player) : Player → Pos := fun o => if o = p then col p 2 else col p 4
-- A one-step move off the file (the same square for both owners).
private def step : Pos := (1, 2)

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

private theorem after_grid (p : Player) (dst q : Pos) (hd : dst ≠ col p 2) :
    (applyMove (initial p) (kingMove p dst)).board.grid q =
      if q = dst then some ⟨p, .king⟩
      else if q = col p 2 then none else (initial p).board.grid q := by
  unfold kingMove
  by_cases hq : q = dst
  · subst q
    rw [ite_eq_left rfl, applyMove_boardMove_grid_dst]
    cases p <;> rfl
  · by_cases hs : q = col p 2
    · subst q
      rw [ite_eq_right hq, ite_eq_left rfl]
      exact applyMove_boardMove_grid_src (initial p) (col p 2) dst false (Ne.symm hd)
    · rw [ite_eq_right hq, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (initial p) (col p 2) dst false q hs hq

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
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd
  · cases hp; cases p <;> cases ho

-- After the king leaves the file, the enemy king is too far to attack it.
private theorem after_safe (p : Player) (dst : Pos) (hd2 : dst ≠ col p 2)
    (hfar : Pos.dirTo (col p 4) dst ∉ PieceType.king.stepDirs.map (Dir.forPlayer · p.opponent)) :
    ¬ inCheckOriented (applyMove (initial p) (kingMove p dst)).board p dst := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [after_grid p dst pos hd2] at hp
  dsimp only [initial] at hp
  split_ifs at hp <;> cases hp
  all_goals first
    | (cases p <;> cases ho; done)
    | (rename_i h; subst h
       rcases ha with hs | ⟨_, hsd, _⟩
       · exact hfar hs
       · simp [PieceType.slideDirs] at hsd)

private theorem rook_check (p : Player) (dst : Pos) (hd1 : dst ≠ col p 1) (hd2 : dst ≠ col p 2)
    (hd3 : dst ≠ col p 3) (hd0 : col p 0 ≠ dst) :
    inCheckOriented (applyMove (initial p) (kingMove p dst)).board p.opponent (col p 4) := by
  refine ⟨col p 0, ⟨p, .rook⟩, ?_, by cases p <;> rfl, ?_⟩
  · rw [after_grid p dst _ hd2, ite_eq_right hd0, ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · refine (col_attack _ p).mpr ((col_clear _ p).mpr ⟨?_, ?_, ?_⟩)
    · rw [after_grid p dst _ hd2, ite_eq_right (Ne.symm hd1), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl
    · rw [after_grid p dst _ hd2, ite_eq_right (Ne.symm hd2), ite_eq_left rfl]
    · rw [after_grid p dst _ hd2, ite_eq_right (Ne.symm hd3), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl

private def premisesOf (p : Player) (dst : Pos) : Prop :=
  let tr := MoveTrace.single (initial p) (kingMove p dst)
  let kp := tr.kingPositionsFrom (positions p)
  tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧ tr.KingsWellPlaced kp ∧
    tr.EveryMoveLeavesOwnKingSafe kp ∧ tr.InitialOpponentKingSafe kp ∧
    tr.EveryMoveChecksOpponent kp

-- All transition and safety premises and every move checking, for any destination off the
-- file and away from the enemy king.
private theorem premises (p : Player) (dst : Pos) (hd0 : col p 0 ≠ dst) (hd1 : dst ≠ col p 1)
    (hd2 : dst ≠ col p 2) (hd3 : dst ≠ col p 3) (hd4 : dst ≠ col p 4)
    (hfar : Pos.dirTo (col p 4) dst ∉ PieceType.king.stepDirs.map (Dir.forPlayer · p.opponent)) :
    premisesOf p dst := by
  dsimp only [premisesOf]
  let tr := MoveTrace.single (initial p) (kingMove p dst)
  have ht := MoveTrace.single_followsTransitions (initial p) (kingMove p dst)
  have hempty : (initial p).board.grid dst = none := by
    dsimp only [initial]
    rw [ite_eq_right (Ne.symm hd0), ite_eq_right hd2, ite_eq_right hd4]
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst' pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (col p 2) dst false = .boardMove src dst' pr at hm
    cases hm
    exact ⟨⟨p, .king⟩, by cases p <;> rfl, rfl⟩
  · apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions p) ht
    · intro i o; have hi := Fin.eq_zero i; subst i
      change (initial p).board.grid dst ≠ some ⟨o, .king⟩
      rw [hempty]
      exact nofun
    · intro i pt dst' hm; change Move.boardMove _ _ _ = .dropMove pt dst' at hm; cases hm
    · exact placed p
  · intro i; have hi := Fin.eq_zero i; subst i
    have h := after_safe p dst hd2 hfar
    cases p
    · exact h
    · exact h
  · cases p
    exacts [start_safe .sente, start_safe .gote]
  · intro i; have hi := Fin.eq_zero i; subst i
    have h := rook_check p dst hd1 hd2 hd3 hd0
    cases p
    · exact h
    · exact h

/-! ## The king's discovered check -/

private def tr (p : Player) : MoveTrace := MoveTrace.single (initial p) (kingMove p step)
private def kpT (p : Player) := (tr p).kingPositionsFrom (positions p)

-- Both first movers. The king's step is a discovered check that moves the
-- non-glaring king, and the trace is not periodic.
example (p : Player) : (tr p).OpenableMoveBy (kpT p) p .king ∧ ¬ (tr p).IsPeriodic := by
  obtain ⟨ht, hs, hk, hsafe, h0, hc⟩ :=
    premises p step (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
      (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  have hm : (tr p).moves (0 : Fin 1) =
      .boardMove (kpT p (0 : Fin 1).castSucc ((tr p).before (0 : Fin 1)).turn) step false := by
    cases p <;> rfl
  have hu := (tr p).kingMove_unblockedChecker (kpT p) ht hs hk hsafe h0 hc (0 : Fin 1) step false hm
  refine ⟨⟨(0 : Fin 1), col p 2, step, false, rfl, rfl, by cases p <;> rfl, fun hg =>
    (tr p).not_unblockedChecker_of_source_glares (kpT p) ht hs hk hsafe h0 (0 : Fin 1) (col p 2)
      step false rfl hg hu, hu⟩, ?_⟩
  intro h
  have hturn := congrArg BoardState.turn h
  change p.opponent = p at hturn
  cases p <;> cases hturn

/-! ## Piece counts -/

-- Only the rook on `col p 0` is a rook or dragon, and there are no bishops.
private theorem counts (p : Player) (k : Fin 2) :
    ((tr p).bishopHorseSquares k).card ≤ 2 ∧ ((tr p).rookDragonSquares k).card ≤ 2 := by
  have hgrid : ∀ q : Pos, ((tr p).states k).board.grid q = (initial p).board.grid q ∨
      ((tr p).states k).board.grid q =
        (applyMove (initial p) (kingMove p step)).board.grid q := by
    intro q
    match k with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
  have hpieces : ∀ q (piece : Piece), ((tr p).states k).board.grid q = some piece →
      (q = col p 0 ∧ piece = ⟨p, .rook⟩) ∨ piece.pieceType = .king := by
    intro q piece hq
    rcases hgrid q with h | h <;> rw [h] at hq
    · dsimp only [initial] at hq
      split_ifs at hq with h1 h2 h3 <;> cases hq
      · exact Or.inl ⟨h1, rfl⟩
      · exact Or.inr rfl
      · exact Or.inr rfl
    · rw [after_grid p step q (by cases p <;> decide)] at hq
      dsimp only [initial] at hq
      split_ifs at hq with h1 h2 h3 h4 <;> cases hq
      · exact Or.inr rfl
      · exact Or.inl ⟨h3, rfl⟩
      · exact Or.inr rfl
  constructor
  · rw [show (tr p).bishopHorseSquares k = ∅ from ?_]
    · simp
    · ext q
      simp only [MoveTrace.bishopHorseSquares, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      rintro ⟨piece, hq, ht⟩
      rcases hpieces q piece hq with ⟨_, rfl⟩ | hk
      · rcases ht with h | h <;> cases h
      · rcases ht with h | h <;> rw [hk] at h <;> cases h
  · calc ((tr p).rookDragonSquares k).card ≤ ({col p 0} : Finset Pos).card := by
          apply Finset.card_le_card
          intro q hq
          simp only [MoveTrace.rookDragonSquares, Finset.mem_filter, Finset.mem_univ,
            true_and] at hq
          obtain ⟨piece, hq, ht⟩ := hq
          rcases hpieces q piece hq with ⟨rfl, _⟩ | hk
          · exact Finset.mem_singleton_self _
          · rcases ht with h | h <;> rw [hk] at h <;> cases h
      _ ≤ 2 := by simp

example (p : Player) : (tr p).PieceCountsAtMostTwo := fun k => counts p k

end MainTraceTests
end MPC
