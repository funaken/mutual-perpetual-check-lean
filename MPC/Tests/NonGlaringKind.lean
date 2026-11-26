import MPC.Glare.NonGlaringKind
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.NonGlaringKind

Concrete checks for .

- Nothing promotes to a kind that can still promote (`decide` over all kinds).
- For both first movers, a one-move trace in which a silver blocking its own rook
  steps off the file and promotes. The rook gives a discovered check. The trace
  satisfies every premise of the periodic theorems except periodicity:
  - placement, safety, and mutual check;
  - the movement condition (the silver steps diagonally backwards).
  Neither the silver before the move nor the promoted silver after it glares at
  the enemy king, so only the promotion changes the counts.
  - The count of non-glaring silvers drops (`nonGlaringSquaresOf_card_succ_lt`).
  - The count of non-glaring promoted silvers rises. So the reflection condition
    `NonGlaringMoveReflects` is needed for the counts never to rise.
  - The moved piece changes, so the conclusion of
    `afterMove_eq_of_not_glares_of_periodic` fails without periodicity.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed. The silver starts in the enemy camp, so the promotion is legal in
shogi; the board update makes no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Non-glaring kind verification must not import GameSeq"

namespace MPC
namespace NonGlaringKindTests

/-! ## Promotion -/

-- No kind promotes to a silver, a rook, or a bishop.
example (pt : PieceType) :
    pt.promote ≠ .silver ∧ pt.promote ≠ .rook ∧ pt.promote ≠ .bishop :=
  ⟨PieceType.promote_ne_of_promote_ne (by decide), PieceType.promote_ne_of_promote_ne (by decide),
    PieceType.promote_ne_of_promote_ne (by decide)⟩

-- A gold is unchanged by a promoting move; a silver is not.
example (p : Player) : (⟨p, .gold⟩ : Piece).afterMove true = ⟨p, .gold⟩ ∧
    (⟨p, .silver⟩ : Piece).afterMove true ≠ ⟨p, .silver⟩ :=
  ⟨Piece.afterMove_eq_self rfl true, by cases p <;> decide⟩

/-! ## A promoting silver opens its rook's file -/

-- Rank `j` counted from the mover's rook toward the enemy king.
private def y (p : Player) (j : Fin 9) : Fin 9 := if p = .sente then 4 + j else 4 - j
private def rookSq (p : Player) : Pos := (0, y p 0)
private def silverSq (p : Player) : Pos := (0, y p 2)
private def enemySq (p : Player) : Pos := (0, y p 4)
private def dstSq (p : Player) : Pos := (1, y p 1)
private def kingSq (p : Player) : Pos := (8, y p 0)

private def s0 (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = rookSq p then some ⟨p, .rook⟩
        else if q = silverSq p then some ⟨p, .silver⟩
        else if q = kingSq p then some ⟨p, .king⟩
        else if q = enemySq p then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
-- The silver steps diagonally backwards off the file and promotes.
private def promoteMove (p : Player) : Move := .boardMove (silverSq p) (dstSq p) true
private def tr (p : Player) : MoveTrace := MoveTrace.single (s0 p) (promoteMove p)
private def kpc (p : Player) : Fin 2 → Player → Pos :=
  fun _ o => if o = p then kingSq p else enemySq p

private theorem s1_grid (p : Player) (q : Pos) :
    (applyMove (s0 p) (promoteMove p)).board.grid q =
      if q = dstSq p then some ⟨p, .promotedSilver⟩
      else if q = silverSq p then none else (s0 p).board.grid q := by
  unfold promoteMove
  have hd : silverSq p ≠ dstSq p := by cases p <;> decide
  by_cases hq : q = dstSq p
  · subst q
    rw [ite_eq_left rfl, applyMove_boardMove_grid_dst]
    cases p <;> rfl
  · by_cases hs : q = silverSq p
    · subst q
      rw [ite_eq_right hq, ite_eq_left rfl]
      exact applyMove_boardMove_grid_src (s0 p) (silverSq p) (dstSq p) true hd
    · rw [ite_eq_right hq, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (s0 p) (silverSq p) (dstSq p) true q hs hq

private theorem file_clear (b : Board) (p : Player) :
    pathClear b (rookSq p) (enemySq p) ↔
      b.grid (0, y p 1) = none ∧ b.grid (silverSq p) = none ∧ b.grid (0, y p 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (rookSq p) (enemySq p)
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

private theorem file_attack (b : Board) (p : Player) :
    attacksOriented b p .rook (rookSq p) (enemySq p) ↔ pathClear b (rookSq p) (enemySq p) := by
  constructor
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · simp [PieceType.stepDirs] at hs
    · exact hc
  · intro hc
    refine Or.inr ⟨(0, if p = .sente then 1 else -1), ?_, ?_, 4, by decide, ?_, ?_, hc⟩ <;>
      cases p <;> decide

private theorem opponent_ne (p : Player) : p.opponent ≠ p := by
  cases p <;> decide

-- Placement from the two king squares and the absence of other kings.
private theorem placed_of (p : Player) (b : Board)
    (hk : b.grid (kingSq p) = some ⟨p, .king⟩)
    (he : b.grid (enemySq p) = some ⟨p.opponent, .king⟩)
    (hother : ∀ q o, b.grid q = some ⟨o, .king⟩ → q = kingSq p ∨ q = enemySq p) :
    KingsWellPlaced b (fun o => if o = p then kingSq p else enemySq p) := by
  intro o q
  constructor
  · intro h
    rcases hother q o h with rfl | rfl
    · rw [hk] at h
      cases h
      exact (ite_eq_left rfl).symm
    · rw [he] at h
      cases h
      exact (ite_eq_right (opponent_ne p)).symm
  · intro h
    subst h
    by_cases ho : o = p
    · subst ho
      dsimp only
      rw [ite_eq_left rfl]
      exact hk
    · have ho' : o = p.opponent := by cases o <;> cases p <;> first | rfl | exact absurd rfl ho
      subst ho'
      dsimp only
      rw [ite_eq_right ho]
      exact he

private theorem placed0 (p : Player) :
    KingsWellPlaced (s0 p).board (fun o => if o = p then kingSq p else enemySq p) := by
  refine placed_of p _ (by cases p <;> rfl) (by cases p <;> rfl) ?_
  intro q o h
  dsimp only [s0] at h
  split_ifs at h
  all_goals first
    | exact Or.inl ‹_›
    | exact Or.inr ‹_›
    | cases h

private theorem placed1 (p : Player) :
    KingsWellPlaced (applyMove (s0 p) (promoteMove p)).board
      (fun o => if o = p then kingSq p else enemySq p) := by
  refine placed_of p _ ?_ ?_ ?_
  · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · intro q o h
    rw [s1_grid] at h
    dsimp only [s0] at h
    split_ifs at h
    all_goals first
      | exact Or.inl ‹_›
      | exact Or.inr ‹_›
      | cases h

-- Initially the silver blocks the rook, and the silver and the king are too far.
private theorem start_safe (p : Player) :
    ¬ inCheckOriented (s0 p).board p.opponent (enemySq p) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [s0] at hp
  split_ifs at hp with h1 h2 h3 h4 <;> cases hp
  · subst h1
    have h := ((file_clear _ p).mp ((file_attack _ p).mp ha)).2.1
    have hs : (s0 p).board.grid (silverSq p) = some ⟨p, .silver⟩ := by cases p <;> rfl
    rw [hs] at h
    cases h
  · subst h2
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd
  · subst h3
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd
  · cases p <;> cases ho

-- After the move only the enemy king opposes the mover's king, far away.
private theorem after_safe (p : Player) :
    ¬ inCheckOriented (applyMove (s0 p) (promoteMove p)).board p (kingSq p) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [s1_grid] at hp
  dsimp only [s0] at hp
  split_ifs at hp <;> cases hp
  all_goals first
    | (cases p <;> cases ho; done)
    | (rename_i h; subst h
       rcases ha with hs | ⟨_, hsd, _⟩
       · revert hs
         cases p <;> decide
       · simp [PieceType.slideDirs] at hsd)

-- The silver has left the file, so the rook checks the enemy king.
private theorem rook_check (p : Player) :
    inCheckOriented (applyMove (s0 p) (promoteMove p)).board p.opponent (enemySq p) := by
  refine ⟨rookSq p, ⟨p, .rook⟩, ?_, by cases p <;> rfl, ?_⟩
  · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · refine (file_attack _ p).mpr ((file_clear _ p).mpr ⟨?_, ?_, ?_⟩)
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_left rfl]
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl

private def premises (p : Player) : Prop :=
  (tr p).FollowsTransitions ∧ (tr p).BoardMoveSourcesOwned ∧
    (tr p).KingsWellPlaced (kpc p) ∧ (tr p).EveryMoveLeavesOwnKingSafe (kpc p) ∧
    (tr p).InitialOpponentKingSafe (kpc p) ∧ (tr p).EveryMoveChecksOpponent (kpc p) ∧
    (tr p).BoardMovesFollowCanMoveToOriented

-- Every premise of the periodic theorems except periodicity.
private theorem premises_hold (p : Player) : premises p := by
  refine ⟨MoveTrace.single_followsTransitions _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (silverSq p) (dstSq p) true = .boardMove src dst pr at hm
    cases hm
    exact ⟨⟨p, .silver⟩, by cases p <;> rfl, rfl⟩
  · intro k
    match k with
    | ⟨0, _⟩ => exact placed0 p
    | ⟨1, _⟩ => exact placed1 p
  · intro i; have hi := Fin.eq_zero i; subst i
    have h := after_safe p
    cases p
    · exact h
    · exact h
  · have h := start_safe p
    cases p
    · exact h
    · exact h
  · intro i; have hi := Fin.eq_zero i; subst i
    have h := rook_check p
    cases p
    · exact h
    · exact h
  · intro i src dst pr piece hm hp; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (silverSq p) (dstSq p) true = .boardMove src dst pr at hm
    cases hm
    change (s0 p).board.grid (silverSq p) = some piece at hp
    have hp' : (s0 p).board.grid (silverSq p) = some ⟨p, .silver⟩ := by cases p <;> rfl
    rw [hp'] at hp
    cases hp
    exact Or.inl (by cases p <;> decide)

-- The silver, two squares from the enemy king, does not glare.
private theorem silver_not_glares (p : Player) :
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (0 : Fin 2) (silverSq p) := by
  rintro ⟨piece, hp, ha⟩
  change (s0 p).board.grid (silverSq p) = some piece at hp
  have hp' : (s0 p).board.grid (silverSq p) = some ⟨p, .silver⟩ := by cases p <;> rfl
  rw [hp'] at hp
  cases hp
  rcases ha with hs | ⟨_, hsd, _⟩
  · revert hs
    cases p <;> decide
  · simp [PieceType.slideDirs] at hsd

-- The promoted silver, three ranks from the enemy king, does not glare either.
private theorem promoted_not_glares (p : Player) :
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (1 : Fin 2) (dstSq p) := by
  rintro ⟨piece, hp, ha⟩
  change (applyMove (s0 p) (promoteMove p)).board.grid (dstSq p) = some piece at hp
  rw [s1_grid, ite_eq_left rfl] at hp
  cases hp
  rcases ha with hs | ⟨_, hsd, _⟩
  · revert hs
    cases p <;> decide
  · simp [PieceType.slideDirs] at hsd

private theorem not_periodic (p : Player) : ¬ (tr p).IsPeriodic := by
  intro h
  have ht := congrArg BoardState.turn h
  change p.opponent = p at ht
  cases p <;> cases ht

-- Both first movers. Every premise but periodicity holds, the trace is not
-- periodic, the silver and the promoted silver do not glare, the moved piece
-- changes, and the count of non-glaring silvers drops.
example (p : Player) :
    premises p ∧ ¬ (tr p).IsPeriodic ∧
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (0 : Fin 2) (silverSq p) ∧
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (1 : Fin 2) (dstSq p) ∧
    (⟨p, .silver⟩ : Piece).afterMove true ≠ ⟨p, .silver⟩ ∧
    ((tr p).nonGlaringSquaresOf (kpc p) (fun x => x = ⟨p, .silver⟩) (1 : Fin 2)).card <
      ((tr p).nonGlaringSquaresOf (kpc p) (fun x => x = ⟨p, .silver⟩) (0 : Fin 2)).card := by
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr⟩ := premises_hold p
  have hd := (tr p).boardMoveEndpointsDistinct_of_oriented hs hr
  refine ⟨⟨ht, hs, hk, hsafe, h0, hc, hr⟩, not_periodic p, silver_not_glares p,
    promoted_not_glares p, by cases p <;> decide, ?_⟩
  refine (tr p).nonGlaringSquaresOf_card_succ_lt (kpc p) ht hs hk hsafe h0 hc hd _ (0 : Fin 1) rfl
    (fun _ _ _ _ _ _ _ hx =>
      Piece.eq_of_afterMove_eq (show PieceType.silver.promote ≠ .silver by decide) hx)
    (silverSq p) (dstSq p) true rfl ?_ ?_
  · refine ((tr p).mem_nonGlaringSquaresOf (kpc p) _ _ _).mpr
      ⟨⟨⟨p, .silver⟩, ?_, rfl⟩, silver_not_glares p⟩
    change (s0 p).board.grid (silverSq p) = _
    cases p <;> rfl
  · intro hmem
    obtain ⟨⟨x, hx, hxe⟩, _⟩ := ((tr p).mem_nonGlaringSquaresOf (kpc p) _ _ _).mp hmem
    change (applyMove (s0 p) (promoteMove p)).board.grid (dstSq p) = some x at hx
    rw [s1_grid, ite_eq_left rfl] at hx
    cases hx
    have hxe' : (⟨p, .promotedSilver⟩ : Piece) = ⟨p, .silver⟩ := hxe
    cases hxe'

-- Without periodicity a promoted kind can gain a non-glaring piece: the count of
-- non-glaring promoted silvers rises, so the reflection condition is needed.
example (p : Player) :
    ((tr p).nonGlaringSquaresOf (kpc p) (fun x => x = ⟨p, .promotedSilver⟩) (0 : Fin 2)).card <
      ((tr p).nonGlaringSquaresOf (kpc p) (fun x => x = ⟨p, .promotedSilver⟩)
        (1 : Fin 2)).card := by
  have hempty : (tr p).nonGlaringSquaresOf (kpc p) (fun x => x = ⟨p, .promotedSilver⟩)
      (0 : Fin 2) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨⟨x, hx, hxe⟩, _⟩ := ((tr p).mem_nonGlaringSquaresOf (kpc p) _ _ _).mp hq
    have hxe' : x = ⟨p, .promotedSilver⟩ := hxe
    subst hxe'
    change (s0 p).board.grid q = some ⟨p, .promotedSilver⟩ at hx
    dsimp only [s0] at hx
    split_ifs at hx <;> simp at hx
  rw [hempty, Finset.card_empty]
  refine Finset.card_pos.mpr ⟨dstSq p, ((tr p).mem_nonGlaringSquaresOf (kpc p) _ _ _).mpr
    ⟨⟨⟨p, .promotedSilver⟩, ?_, rfl⟩, promoted_not_glares p⟩⟩
  change (applyMove (s0 p) (promoteMove p)).board.grid (dstSq p) = _
  rw [s1_grid, ite_eq_left rfl]

end NonGlaringKindTests
end MPC
