import MPC.Chess.CheckingRaySeparation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite enumeration of the nonparallel checking-ray intersections. Under
positive-length periodic checking, king-line exclusion makes it complete. -/

namespace MPC.Chess.MoveTrace

/-- Solver outputs for all pairs of actual checking directions, with duplicates
removed. For arbitrary traces this omits parallel overlaps. -/
def checkingCrossings (tr : MoveTrace) (kp : Color → Pos) : Finset PlanePoint :=
  Finset.univ.biUnion fun dw => Finset.univ.biUnion fun db =>
    if tr.CheckingRay (kp .white) .white dw ∧ tr.CheckingRay (kp .black) .black db then
      (nonparallelIntersection (kp .white).toPlane (kp .black).toPlane dw db).toFinset
    else ∅

theorem mem_checkingCrossings_iff (tr : MoveTrace) (kp : Color → Pos) (p : PlanePoint) :
    p ∈ tr.checkingCrossings kp ↔ ∃ dw db,
      tr.CheckingRay (kp .white) .white dw ∧ tr.CheckingRay (kp .black) .black db ∧
      nonparallelIntersection (kp .white).toPlane (kp .black).toPlane dw db = some p := by
  simp only [checkingCrossings, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨dw, db, h⟩
    split_ifs at h with hc
    · exact ⟨dw, db, hc.1, hc.2, Option.mem_toFinset.mp h⟩
    · exact False.elim (Finset.notMem_empty _ h)
  · rintro ⟨dw, db, hw, hb, hi⟩
    refine ⟨dw, db, ?_⟩
    rw [ite_eq_left ⟨hw, hb⟩, hi]
    simp

theorem checkingCrossing_of_mem_checkingCrossings (tr : MoveTrace) (kp : Color → Pos)
    (p : PlanePoint) (h : p ∈ tr.checkingCrossings kp) : tr.CheckingCrossing kp p := by
  obtain ⟨dw, db, hw, hb, hi⟩ := (tr.mem_checkingCrossings_iff kp p).mp h
  exact tr.checkingCrossing_of_nonparallelIntersection kp p dw db hw hb hi

/-- The trace hypotheses exclude overlaps; no extra geometric separation or
existence assumption is imposed on the finite enumeration. -/
theorem mem_checkingCrossings_iff_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (p : PlanePoint) :
    p ∈ tr.checkingCrossings (kp 0) ↔ tr.CheckingCrossing (kp 0) p := by
  rw [tr.mem_checkingCrossings_iff,
    tr.checkingCrossing_iff_nonparallelIntersection_of_periodic_checks kp hl hk hc hp hn]

theorem checkingCrossings_finite_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) :
    Set.Finite {p | tr.CheckingCrossing (kp 0) p} := by
  have he : {p | tr.CheckingCrossing (kp 0) p} = (tr.checkingCrossings (kp 0) : Set PlanePoint) := by
    ext p
    exact (tr.mem_checkingCrossings_iff_of_periodic_checks kp hl hk hc hp hn p).symm
  rw [he]
  exact Finset.finite_toSet _

/-- A uniform bound from the eight possible directions at each king. It does
not assert that any particular ray contains two crossings. -/
theorem checkingCrossings_card_le (tr : MoveTrace) (kp : Color → Pos) :
    (tr.checkingCrossings kp).card ≤ 64 := by
  unfold checkingCrossings
  calc
    _ ≤ ∑ dw : RayDirection, ∑ db : RayDirection,
        (if tr.CheckingRay (kp .white) .white dw ∧ tr.CheckingRay (kp .black) .black db then
          (nonparallelIntersection (kp .white).toPlane (kp .black).toPlane dw db).toFinset
        else ∅).card := le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum fun _ _ =>
          Finset.card_biUnion_le)
    _ ≤ ∑ _dw : RayDirection, ∑ _db : RayDirection, 1 := by
      apply Finset.sum_le_sum
      intro dw _
      apply Finset.sum_le_sum
      intro db _
      split_ifs
      · cases nonparallelIntersection (kp .white).toPlane (kp .black).toPlane dw db <;> simp
      · simp
    _ = 64 := by decide

theorem boardMove_mem_checkingCrossings_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    src.toPlane ∈ tr.checkingCrossings (kp 0) ∧ dst.toPlane ∈ tr.checkingCrossings (kp 0) := by
  have hn : 0 < tr.len := Nat.zero_lt_of_lt i.isLt
  rw [tr.mem_checkingCrossings_iff_of_periodic_checks kp hl hk hc hp hn,
    tr.mem_checkingCrossings_iff_of_periodic_checks kp hl hk hc hp hn]
  exact tr.boardMove_checkingCrossings_of_periodic_checks kp hl hk hc hp i src dst hm

end MPC.Chess.MoveTrace
