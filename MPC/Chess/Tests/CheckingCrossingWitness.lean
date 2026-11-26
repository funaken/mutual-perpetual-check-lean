import MPC.Chess.CheckingCrossingWitness
import Mathlib.Tactic.FinCases

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

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

-- Every arrival in this legal knight cycle departs exactly two moves later,
-- modulo the period. This covers both colors and both wraparound arrivals.
-- It is not a mutual-check cycle; the departure theorem does not need one.
example (c : Color) (i : Fin 4) :
    ∃ (src A dst : Pos) (j : Fin 4),
      (returnTrace c).moves i = .boardMove src A none ∧
      (returnTrace c).moves j = .boardMove A dst none ∧
      ((returnTrace c).before j).board A = ((returnTrace c).after i).board A ∧
      ((returnTrace c).before j).turn = ((returnTrace c).before i).turn ∧
      j.val = (i.val + 2) % 4 := by
  obtain ⟨src, A, hm⟩ := return_ordinary c i
  obtain ⟨j, dst, hmj, hboard, hturn⟩ := (returnTrace c).arrival_piece_departs_of_periodic
    (return_legal c) (return_periodic c) (return_ordinary c) i src A hm
  refine ⟨src, A, dst, j, hm, hmj, hboard, hturn, ?_⟩
  clear hboard hturn
  fin_cases i <;> simp [returnTrace, returnMove] at hm
  all_goals rcases hm with ⟨rfl, rfl⟩
  all_goals
    fin_cases j <;> cases c <;>
      simp [returnTrace, returnMove, Color.homeRank, Color.doubleStepTargetRank, Color.opponent] at hmj ⊢

private def oneTrace (c : Color) : MoveTrace :=
  .single (returnState c 0) (returnState c 1) (returnMove c 0)

-- A legal one-move prefix does not return to its board and its arrival need
-- never depart. Recurrence is essential even for the material-only lemma.
example (c : Color) : (oneTrace c).FollowsLegalMoves ∧
    ¬ (oneTrace c).BoardTurnPeriodic ∧
    ¬ ∃ (j : Fin 1) (dst : Pos),
      (oneTrace c).moves j = .boardMove (2, c.doubleStepTargetRank) dst none := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := Fin.eq_zero i
    subst i
    exact return_legal c (0 : Fin 4)
  · intro h
    have ht := h.2
    cases c <;> contradiction
  · rintro ⟨j, dst, hm⟩
    have he := (Move.boardMove.inj hm).1
    cases c <;> have hx := congrArg (fun q : Pos => q.1.val) he <;> norm_num [oneTrace, returnMove] at hx

private def singletonKings (c : Color) : Color → Pos := fun owner => if owner = c then (0, 0) else (2, 0)
private def singletonBoard (c : Color) : Board := fun q =>
  if q = (0, 0) then some ⟨c, .king⟩
  else if q = (2, 0) then some ⟨c.opponent, .king⟩
  else if q = (2, 2) then some ⟨c.opponent, .bishop⟩
  else if q = (0, 2) then some ⟨c, .bishop⟩ else none
private def singletonTrace (c : Color) : MoveTrace := .empty ⟨singletonBoard c, c, {}, none⟩

private theorem singleton_rays (c owner : Color) (d : RayDirection) :
    (singletonTrace c).CheckingRay (singletonKings c owner) owner d ↔
      (owner = c ∧ d = .northEast) ∨ (owner = c.opponent ∧ d = .northWest) := by
  cases c <;> cases owner <;> cases d <;> decide

private theorem singleton_crossings (c : Color) :
    (singletonTrace c).checkingCrossings (singletonKings c) = {(1, 1)} := by
  ext p
  rw [MoveTrace.mem_checkingCrossings_iff]
  simp only [singleton_rays]
  cases c <;> simp [Color.opponent, singletonKings] <;>
    norm_num [nonparallelIntersection, rayIntersectionParameters, rayOffset, rayDet,
      rayPoint, RayDirection.vector, Pos.toPlane, Pos.toInt, Fin.coe_ofNat_eq_mod] <;> exact eq_comm

-- With length zero all the other trace conditions hold, but a checking ray
-- has just one crossing. The positive-length premise cannot be dropped.
example (c : Color) :
    (singletonTrace c).FollowsLegalMoves ∧
    (singletonTrace c).KingsWellPlaced (fun _ => singletonKings c) ∧
    (singletonTrace c).EveryMoveChecksOpponent (fun _ => singletonKings c) ∧
    (singletonTrace c).BoardTurnPeriodic ∧ (singletonTrace c).len = 0 ∧
    (singletonTrace c).CheckingRay (singletonKings c c) c .northEast ∧
    ¬ ∃ A B : Pos, A ≠ B ∧
      A.toPlane ∈ (singletonTrace c).checkingCrossings (singletonKings c) ∧
      B.toPlane ∈ (singletonTrace c).checkingCrossings (singletonKings c) := by
  refine ⟨(fun i => Fin.elim0 i), ?_, (fun i => Fin.elim0 i), ⟨rfl, rfl⟩, rfl, ?_, ?_⟩
  · unfold MoveTrace.KingsWellPlaced MPC.Chess.KingsWellPlaced
    cases c <;> decide
  · apply (singleton_rays c c .northEast).mpr
    exact Or.inl ⟨rfl, rfl⟩
  · rintro ⟨A, B, hne, hA, hB⟩
    rw [singleton_crossings] at hA hB
    have he := (Finset.mem_singleton.mp hA).trans (Finset.mem_singleton.mp hB).symm
    exact hne (Pos.toPlane_injective he)

private def near : RayDirection → Pos
  | .north => (3, 4) | .northEast => (4, 4) | .east => (4, 3) | .southEast => (4, 2)
  | .south => (3, 2) | .southWest => (2, 2) | .west => (2, 3) | .northWest => (2, 4)
private def far : RayDirection → Pos
  | .north => (3, 6) | .northEast => (6, 6) | .east => (6, 3) | .southEast => (6, 0)
  | .south => (3, 0) | .southWest => (0, 0) | .west => (0, 3) | .northWest => (0, 6)
private def sliderBoard (c : Color) (d : RayDirection) : Board := fun q =>
  if q = far d then some ⟨c.opponent, .queen⟩ else none
private def blockedBoard (c : Color) (d : RayDirection) : Board := fun q =>
  if q = near d then some ⟨c, .knight⟩ else sliderBoard c d q

-- Across all eight directions, moving the only blocker off the ray restores
-- the retained queen's attack. These local boards do not claim legal periods.
example (c : Color) (d : RayDirection) :
    Between (far d) (3, 3) (near d) ∧
    attacks (sliderBoard c d) ⟨c.opponent, .queen⟩ (far d) (3, 3) ∧
    ¬ attacks (blockedBoard c d) ⟨c.opponent, .queen⟩ (far d) (3, 3) ∧
    attacks ((blockedBoard c d).relocate (near d) (near d.opposite) none)
      ⟨c.opponent, .queen⟩ (far d) (3, 3) := by
  cases c <;> cases d <;> decide

end MPC.Chess.Tests
