import MPC.Chess.CheckingRayMoves
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def nearRay : RayDirection → Pos
  | .north => (3, 4) | .northEast => (4, 4) | .east => (4, 3) | .southEast => (4, 2)
  | .south => (3, 2) | .southWest => (2, 2) | .west => (2, 3) | .northWest => (2, 4)
private def farRay : RayDirection → Pos
  | .north => (3, 6) | .northEast => (6, 6) | .east => (6, 3) | .southEast => (6, 0)
  | .south => (3, 0) | .southWest => (0, 0) | .west => (0, 3) | .northWest => (0, 6)

example : Fintype.card RayDirection = 8 := by decide

example (d : RayDirection) : OnRay (3, 3) d (nearRay d) ∧ OnRay (3, 3) d (farRay d) ∧
    ¬ OnRay (3, 3) d (3, 3) := by cases d <;> decide

example (d : RayDirection) : Between (farRay d) (3, 3) (nearRay d) := by
  have hn : OnRay (3, 3) d (nearRay d) := by cases d <;> decide
  have hf : OnRay (3, 3) d (farRay d) := by cases d <;> decide
  apply (hf.between_iff_distance hn).mpr
  cases d <;> decide

example : OnRay (0, 0) .north (0, 7) ∧ OnRay (7, 7) .southWest (0, 0) ∧
    OnRay (3, 3) .north (3, 4) ∧ OnRay (3, 3) .south (3, 2) ∧
    ¬ OnRay (3, 3) .north (3, 2) ∧ ¬ ∃ d, OnRay (0, 0) d (1, 2) := by decide

-- The geometric crossing argument applies in all eight orientations.
example (d : RayDirection) :
    Between (nearRay d) (farRay d) (match d with
      | .north => (3, 5) | .northEast => (5, 5) | .east => (5, 3) | .southEast => (5, 1)
      | .south => (3, 1) | .southWest => (1, 1) | .west => (1, 3) | .northWest => (1, 5)) := by
  apply between_of_same_ray_exit (d := d) (k := (3, 3))
  all_goals cases d <;> decide

private def rayBoard (kingOwner checkerOwner : Color) : Board := fun q =>
  if q = (0, 0) then some ⟨kingOwner, .king⟩
  else if q = (7, 7) then some ⟨kingOwner.opponent, .king⟩
  else if q = (0, 7) then some ⟨checkerOwner, .rook⟩ else none

private def rayKings (c : Color) : Color → Pos := fun o => if o = c then (0, 0) else (7, 7)

-- A zero-length trace can already contain a real check. CheckingRay quantifies
-- over states, not moves; the eventual all-moves theorem is vacuous at length 0.
example (c : Color) :
    let tr := MoveTrace.empty ⟨rayBoard c c.opponent, c, {}, none⟩
    tr.KingsWellPlaced (fun _ => rayKings c) ∧ tr.CheckingRay (0, 0) c .north := by
  dsimp only
  unfold MoveTrace.KingsWellPlaced MPC.Chess.KingsWellPlaced
  cases c <;> decide

example (c : Color) :
    ∃ d, (MoveTrace.empty ⟨rayBoard c c.opponent, c, {}, none⟩).CheckingRay (0, 0) c d ∧
      OnRay (0, 0) d (0, 7) := by
  apply MoveTrace.exists_checkingRay_of_slider _ 0 (0, 0) (0, 7) c ⟨c.opponent, .rook⟩
  · cases c <;> decide
  · rfl
  · exact Or.inr (Or.inl rfl)
  · cases c <;> decide

example (c : Color) :
    ¬ (MoveTrace.empty ⟨rayBoard c c, c, {}, none⟩).CheckingRay (0, 0) c .north ∧
    ¬ (MoveTrace.empty ⟨Board.empty, c, {}, none⟩).CheckingRay (0, 0) c .north := by
  cases c <;> decide

private def blockedInitial (c : Color) : Position :=
  ⟨(fun q => if q = (0, 3) then some ⟨c, .rook⟩ else rayBoard c c.opponent q), c, {}, none⟩
private def blockedMove : Move := .boardMove (0, 3) (0, 4) none
private def blockedTrace (c : Color) : MoveTrace :=
  .single (blockedInitial c) (applyMove (blockedInitial c) blockedMove) blockedMove

-- A genuinely movable blocker is removed by the stripped board, but remains
-- between the enemy rook and king at every actual state. Glare is insufficient.
example (c : Color) :
    (blockedTrace c).FollowsLegalMoves ∧
    (blockedTrace c).KingsWellPlaced (fun _ => rayKings c) ∧
    (blockedTrace c).GlaresAtEnemyKing (fun _ => rayKings c) 0 (0, 7) ∧
    ¬ (blockedTrace c).CheckingRay (0, 0) c .north := by
  constructor
  · intro i
    refine ⟨rayKings c, ?_, ?_⟩
    · have h : ∀ i : Fin (blockedTrace c).len,
          LegalMove ((blockedTrace c).before i) ((blockedTrace c).moves i) (rayKings c) := by
        cases c <;> decide
      exact h i
    · have hi := Fin.eq_zero i; subst i; rfl
  · unfold MoveTrace.KingsWellPlaced MPC.Chess.KingsWellPlaced
    cases c <;> decide

private def prefixInitial (c : Color) : Position :=
  ⟨(fun q => if q = (0, 3) then some ⟨c.opponent, .rook⟩
    else if q = (0, 7) then none else rayBoard c c.opponent q), c.opponent, {}, none⟩
private def prefixTrace (c : Color) : MoveTrace :=
  .single (prefixInitial c) (applyMove (prefixInitial c) blockedMove) blockedMove

-- Without recurrence a legal checking rook move can stay on the same ray.
example (c : Color) :
    (prefixTrace c).FollowsLegalMoves ∧
    (prefixTrace c).KingsWellPlaced (fun _ => rayKings c) ∧
    (prefixTrace c).EveryMoveChecksOpponent (fun _ => rayKings c) ∧
    ¬ (prefixTrace c).BoardTurnPeriodic ∧
    OnRay (0, 0) .north (0, 3) ∧ OnRay (0, 0) .north (0, 4) := by
  constructor
  · intro i
    refine ⟨rayKings c, ?_, ?_⟩
    · have h : ∀ i : Fin (prefixTrace c).len,
          LegalMove ((prefixTrace c).before i) ((prefixTrace c).moves i) (rayKings c) := by
        cases c <;> decide
      exact h i
    · have hi := Fin.eq_zero i; subst i; rfl
  · constructor
    · unfold MoveTrace.KingsWellPlaced MPC.Chess.KingsWellPlaced
      cases c <;> decide
    constructor
    · unfold MoveTrace.EveryMoveChecksOpponent
      cases c <;> decide
    refine ⟨?_, by decide, by decide⟩
    intro hp
    have ht := hp.2
    cases c <;> contradiction

-- The empty-destination premise of the path lemma matters: capturing an
-- intervening piece on the same ray can create a destination check.
example (c : Color) :
    let b : Board := fun q => if q = (0, 7) then some ⟨c, .rook⟩
      else if q = (0, 3) then some ⟨c.opponent, .knight⟩ else none
    OnRay (0, 0) .north (0, 7) ∧ OnRay (0, 0) .north (0, 3) ∧
    pathClear b (0, 7) (0, 3) ∧ pathClear (b.relocate (0, 7) (0, 3) none) (0, 3) (0, 0) ∧
    ¬ pathClear b (0, 7) (0, 0) := by
  cases c <;> decide

private def returnBoard : Board := fun q =>
  if q = kingHome .white then some ⟨.white, .king⟩
  else if q = kingHome .black then some ⟨.black, .king⟩
  else if q = (1, 0) then some ⟨.white, .knight⟩
  else if q = (1, 7) then some ⟨.black, .knight⟩ else none
private def returnMove (c : Color) : ℕ → Move
  | 0 => .boardMove (1, c.homeRank) (2, c.doubleStepTargetRank) none
  | 1 => .boardMove (1, c.opponent.homeRank) (2, c.opponent.doubleStepTargetRank) none
  | 2 => .boardMove (2, c.doubleStepTargetRank) (1, c.homeRank) none
  | _ => .boardMove (2, c.opponent.doubleStepTargetRank) (1, c.opponent.homeRank) none
private def returnState (c : Color) : ℕ → Position
  | 0 => ⟨returnBoard, c, {}, none⟩
  | n + 1 => applyMove (returnState c n) (returnMove c n)
private def returnTrace (c : Color) : MoveTrace where
  len := 4
  states := fun k => returnState c k.val
  moves := fun i => returnMove c i.val

private theorem return_legal (c : Color) : (returnTrace c).FollowsLegalMoves := by
  intro i
  refine ⟨kingHome, ?_, rfl⟩
  have h : ∀ i : Fin 4, LegalMove (returnState c i.val) (returnMove c i.val) kingHome := by
    cases c <;> decide
  exact h i

private theorem return_ordinary (c : Color) : (returnTrace c).OrdinaryMoves := by
  intro i
  fin_cases i <;> exact ⟨_, _, rfl⟩

private theorem return_periodic (c : Color) : (returnTrace c).BoardTurnPeriodic := by
  constructor
  · funext q
    have h : ∀ q, (returnState c 4).board q = returnBoard q := by cases c <;> decide
    exact h q
  · cases c <;> rfl

-- Every source has an arrival, including the first and last move. The cycle
-- does not satisfy mutual checking and is not an example of the final premises.
example (c : Color) (i : Fin 4) :
    ∃ src dst, (returnTrace c).moves i = .boardMove src dst none ∧
      ∃ (j : Fin 4) (a : Pos), (returnTrace c).moves j = .boardMove a src none := by
  obtain ⟨src, dst, hm⟩ := return_ordinary c i
  exact ⟨src, dst, hm, (returnTrace c).source_is_destination_of_periodic
    (return_legal c) (return_periodic c) (return_ordinary c) i src dst hm⟩

example (c : Color) : ¬ (returnTrace c).EveryMoveChecksOpponent (fun _ => kingHome) := by
  intro h
  have h0 := h (0 : Fin 4)
  have hn : ¬ inCheck (returnState c 1).board c.opponent (kingHome c.opponent) := by cases c <;> decide
  exact hn h0

end MPC.Chess.Tests
