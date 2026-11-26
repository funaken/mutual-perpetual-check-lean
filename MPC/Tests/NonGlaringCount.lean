import MPC.Glare.NonGlaringCount
import Lean
/-!
# MPC.Tests.NonGlaringCount

Lemmas 2.8 and 2.9 need periodicity. For both first movers, a one-move trace has
a gold step forward to capture a pawn and check the enemy king. It satisfies
every other premise: placement, safety, mutual check, and the movement
condition. Yet a non-glaring gold moves to a glaring square, and the captured
pawn did not glare, so both lemmas' conclusions fail. The count of non-glaring
squares drops, by both strict-decrease theorems. Whether mutual check or the
movement condition is needed for the periodic lemmas is not exhibited. The board
update makes no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Non-glaring count verification must not import GameSeq"

namespace MPC
namespace NonGlaringCountTests

-- Rank `j` from the first mover's side.
private def y (p : Player) (j : Fin 9) : Fin 9 := if p = .sente then j else 8 - j
private def kingSq (p : Player) : Pos := (0, y p 0)
private def goldSq (p : Player) : Pos := (4, y p 2)
private def pawnSq (p : Player) : Pos := (4, y p 3)
private def enemySq (p : Player) : Pos := (4, y p 4)

private def s0 (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = kingSq p then some ⟨p, .king⟩
        else if q = goldSq p then some ⟨p, .gold⟩
        else if q = pawnSq p then some ⟨p.opponent, .pawn⟩
        else if q = enemySq p then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
-- The gold steps forward, capturing the pawn and checking the enemy king.
private def capture (p : Player) : Move := .boardMove (goldSq p) (pawnSq p) false
private def tr (p : Player) : MoveTrace := MoveTrace.single (s0 p) (capture p)
private def kpc (p : Player) : Fin 2 → Player → Pos :=
  fun _ o => if o = p then kingSq p else enemySq p

private theorem s1_grid (p : Player) (q : Pos) :
    (applyMove (s0 p) (capture p)).board.grid q =
      if q = pawnSq p then some ⟨p, .gold⟩
      else if q = goldSq p then none else (s0 p).board.grid q := by
  unfold capture
  have hd : goldSq p ≠ pawnSq p := by cases p <;> decide
  by_cases hq : q = pawnSq p
  · subst q
    rw [ite_eq_left rfl, applyMove_boardMove_grid_dst]
    cases p <;> rfl
  · by_cases hs : q = goldSq p
    · subst q
      rw [ite_eq_right hq, ite_eq_left rfl]
      exact applyMove_boardMove_grid_src (s0 p) (goldSq p) (pawnSq p) false hd
    · rw [ite_eq_right hq, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (s0 p) (goldSq p) (pawnSq p) false q hs hq

private theorem opponent_ne (p : Player) : p.opponent ≠ p := by
  cases p <;> decide

-- Placement from the two king squares and the absence of other kings.
private theorem placed_of (p : Player) (b : Board)
    (hk : b.grid (kingSq p) = some ⟨p, .king⟩) (he : b.grid (enemySq p) = some ⟨p.opponent, .king⟩)
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
    KingsWellPlaced (applyMove (s0 p) (capture p)).board
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

-- Initially the gold is two squares from the enemy king and the kings are apart.
private theorem start_safe (p : Player) :
    ¬ inCheckOriented (s0 p).board p.opponent (enemySq p) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [s0] at hp
  split_ifs at hp <;> cases hp
  all_goals first
    | (cases p <;> cases ho; done)
    | (rename_i h; subst h
       rcases ha with hs | ⟨_, hsd, _⟩
       · revert hs
         cases p <;> decide
       · simp [PieceType.slideDirs] at hsd)

-- After the capture only the enemy king opposes the mover's king, far away.
private theorem after_safe (p : Player) :
    ¬ inCheckOriented (applyMove (s0 p) (capture p)).board p (kingSq p) := by
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

-- The gold now stands directly in front of the enemy king.
private theorem gold_attacks (p : Player) :
    attacksOriented (applyMove (s0 p) (capture p)).board p .gold (pawnSq p) (enemySq p) :=
  Or.inl (by cases p <;> decide)

private theorem gold_check (p : Player) :
    inCheckOriented (applyMove (s0 p) (capture p)).board p.opponent (enemySq p) :=
  ⟨pawnSq p, ⟨p, .gold⟩, by rw [s1_grid, ite_eq_left rfl], by cases p <;> rfl, gold_attacks p⟩

private def premises (p : Player) : Prop :=
  (tr p).FollowsTransitions ∧ (tr p).BoardMoveSourcesOwned ∧
    (tr p).KingsWellPlaced (kpc p) ∧ (tr p).EveryMoveLeavesOwnKingSafe (kpc p) ∧
    (tr p).InitialOpponentKingSafe (kpc p) ∧ (tr p).EveryMoveChecksOpponent (kpc p) ∧
    (tr p).BoardMovesFollowCanMoveToOriented

-- Every premise of Lemmas 2.8 and 2.9 except periodicity.
private theorem premises_hold (p : Player) : premises p := by
  refine ⟨MoveTrace.single_followsTransitions _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (goldSq p) (pawnSq p) false = .boardMove src dst pr at hm
    cases hm
    exact ⟨⟨p, .gold⟩, by cases p <;> rfl, rfl⟩
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
    have h := gold_check p
    cases p
    · exact h
    · exact h
  · intro i src dst pr piece hm hp; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (goldSq p) (pawnSq p) false = .boardMove src dst pr at hm
    cases hm
    change (s0 p).board.grid (goldSq p) = some piece at hp
    have hp' : (s0 p).board.grid (goldSq p) = some ⟨p, .gold⟩ := by cases p <;> rfl
    rw [hp'] at hp
    cases hp
    exact Or.inl (by cases p <;> decide)

-- Initially the gold, two squares away, does not glare even on the stripped board.
private theorem gold_not_glares (p : Player) :
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (0 : Fin 2) (goldSq p) := by
  rintro ⟨piece, hp, ha⟩
  change (s0 p).board.grid (goldSq p) = some piece at hp
  have hp' : (s0 p).board.grid (goldSq p) = some ⟨p, .gold⟩ := by cases p <;> rfl
  rw [hp'] at hp
  cases hp
  rcases ha with hs | ⟨_, hsd, _⟩
  · revert hs
    cases p <;> decide
  · simp [PieceType.slideDirs] at hsd

-- The pawn only covers the gold's square, not the mover's king.
private theorem pawn_not_glares (p : Player) :
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (0 : Fin 2) (pawnSq p) := by
  rintro ⟨piece, hp, ha⟩
  change (s0 p).board.grid (pawnSq p) = some piece at hp
  have hp' : (s0 p).board.grid (pawnSq p) = some ⟨p.opponent, .pawn⟩ := by cases p <;> rfl
  rw [hp'] at hp
  cases hp
  rcases ha with hs | ⟨_, hsd, _⟩
  · revert hs
    cases p <;> decide
  · simp [PieceType.slideDirs] at hsd

private theorem gold_glares (p : Player) :
    (tr p).GlaresAtEnemyKing (kpc p) (1 : Fin 2) (pawnSq p) := by
  refine (tr p).glaresAtEnemyKing_of_attacks (kpc p) (1 : Fin 2) (pawnSq p) ⟨p, .gold⟩
    (by change (applyMove (s0 p) (capture p)).board.grid (pawnSq p) = _; rw [s1_grid, ite_eq_left rfl])
    ?_
  have h := gold_attacks p
  cases p
  · exact h
  · exact h

private theorem not_periodic (p : Player) : ¬ (tr p).IsPeriodic := by
  intro h
  have ht := congrArg BoardState.turn h
  change p.opponent = p at ht
  cases p <;> cases ht

-- Both first movers. Every premise but periodicity holds, the trace is not
-- periodic, a non-glaring gold moves to a glaring square (Lemma 2.8 fails), and
-- the captured pawn did not glare (Lemma 2.9 fails). Both strict-decrease
-- theorems apply, so the count of non-glaring squares drops.
example (p : Player) :
    premises p ∧ ¬ (tr p).IsPeriodic ∧
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (0 : Fin 2) (goldSq p) ∧
    (tr p).GlaresAtEnemyKing (kpc p) (1 : Fin 2) (pawnSq p) ∧
    ((tr p).before (0 : Fin 1)).board.grid ((tr p).moves (0 : Fin 1)).destination ≠ none ∧
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (0 : Fin 2) (pawnSq p) ∧
    ((tr p).nonGlaringSquares (kpc p) (1 : Fin 2)).card <
      ((tr p).nonGlaringSquares (kpc p) (0 : Fin 2)).card := by
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr⟩ := premises_hold p
  have hd := (tr p).boardMoveEndpointsDistinct_of_oriented hs hr
  have hocc : ((tr p).before (0 : Fin 1)).board.grid ((tr p).moves (0 : Fin 1)).destination ≠
      none := by
    change (s0 p).board.grid (pawnSq p) ≠ none
    have hp' : (s0 p).board.grid (pawnSq p) = some ⟨p.opponent, .pawn⟩ := by cases p <;> rfl
    rw [hp']
    exact Option.some_ne_none _
  refine ⟨⟨ht, hs, hk, hsafe, h0, hc, hr⟩, not_periodic p, gold_not_glares p, gold_glares p,
    hocc, pawn_not_glares p, ?_⟩
  exact (tr p).nonGlaringSquares_card_succ_lt_of_glares_destination (kpc p) ht hs hk hsafe h0 hc
    hd (0 : Fin 1) rfl (goldSq p) (pawnSq p) false rfl (gold_not_glares p) (gold_glares p)

-- The same drop in the count from the captured pawn alone.
example (p : Player) :
    ((tr p).nonGlaringSquares (kpc p) (1 : Fin 2)).card <
      ((tr p).nonGlaringSquares (kpc p) (0 : Fin 2)).card := by
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr⟩ := premises_hold p
  have hd := (tr p).boardMoveEndpointsDistinct_of_oriented hs hr
  refine (tr p).nonGlaringSquares_card_succ_lt_of_occupied_destination (kpc p) ht hs hk hsafe h0
    hc hd (0 : Fin 1) rfl ?_
  refine ((tr p).mem_nonGlaringSquares (kpc p) _ _).mpr ⟨?_, pawn_not_glares p⟩
  change (s0 p).board.grid (pawnSq p) ≠ none
  have hp' : (s0 p).board.grid (pawnSq p) = some ⟨p.opponent, .pawn⟩ := by cases p <;> rfl
  rw [hp']
  exact Option.some_ne_none _

end NonGlaringCountTests
end MPC
