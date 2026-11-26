import MPC.Chess.CheckingRayHalfPlane

namespace MPC.Chess.Tests

private theorem all_directions : (Finset.univ : Finset RayDirection) =
    {.north, .northEast, .east, .southEast, .south, .southWest, .west, .northWest} := by decide

-- Axis and diagonal boundaries each remove an opposite pair of directions.
example (d : RayDirection) (side : HalfPlaneSide) :
    (halfPlaneDirections (0, 0) (rayPoint (0, 0) d 5) side).card = 3 := by
  cases d <;> cases side <;> norm_num [halfPlaneDirections, all_directions,
    Finset.filter_insert, Finset.filter_singleton, HalfPlaneSide.sign, rayOffset,
    rayPoint, RayDirection.vector]

example : halfPlaneDirections (0, 0) (4, 0) .positive = {.north, .northEast, .northWest} ∧
    halfPlaneDirections (0, 0) (4, 0) .negative = {.south, .southEast, .southWest} ∧
    halfPlaneDirections (0, 0) (3, 1) .positive = {.north, .northEast, .northWest, .west} ∧
    halfPlaneDirections (0, 0) (3, 1) .negative = {.south, .southEast, .southWest, .east} := by
  norm_num [halfPlaneDirections, all_directions, Finset.filter_insert,
    Finset.filter_singleton, HalfPlaneSide.sign, rayOffset, RayDirection.vector]
  decide

-- Reflection and exchanging the kings change the sign but not the count.
example (side : HalfPlaneSide) :
    (halfPlaneDirections (0, 0) (3, 1) side).card = 4 ∧
    (halfPlaneDirections (3, 1) (0, 0) side).card = 4 ∧
    (halfPlaneDirections (0, 0) (3, -1) side).card = 4 := by
  cases side <;> norm_num [halfPlaneDirections, all_directions,
    Finset.filter_insert, Finset.filter_singleton, HalfPlaneSide.sign, rayOffset, RayDirection.vector]

-- Boundary points, including both origins and extensions of the king line,
-- are in neither side. Coincident origins do not satisfy the count theorem.
example (side : HalfPlaneSide) :
    ¬ InKingHalfPlane (0, 0) (3, 1) side (0, 0) ∧
    ¬ InKingHalfPlane (0, 0) (3, 1) side (3, 1) ∧
    ¬ InKingHalfPlane (0, 0) (3, 1) side (9, 3) ∧
    halfPlaneDirections (2, 2) (2, 2) side = ∅ := by
  cases side <;> norm_num [halfPlaneDirections, HalfPlaneSide.sign,
    rayOffset, halfPlaneCross, InKingHalfPlane]

example : InKingHalfPlane (0, 0) (3, 1) .positive (0, 1) ∧
    ¬ InKingHalfPlane (0, 0) (3, 1) .negative (0, 1) ∧
    InKingHalfPlane (3, 1) (0, 0) .negative (0, 1) := by
  norm_num [HalfPlaneSide.sign, halfPlaneCross, InKingHalfPlane]

-- Both boundary origins use the same global direction classification.
example (d : RayDirection) (side : HalfPlaneSide) (t : ℚ) (ht : 0 < t) :
    InKingHalfPlane (0, 0) (3, 1) side (rayPoint (3, 1) d t) ↔
      d ∈ halfPlaneDirections (0, 0) (3, 1) side :=
  inKingHalfPlane_rayPoint_iff _ _ _ side d t (by norm_num [halfPlaneCross]) ht

-- A non-lattice crossing; origin and negative parameters need separate handling.
example : OnRationalRay (0, 0) .northEast (1/2, 1/2) ∧
    OnRationalRay (1, 0) .northWest (1/2, 1/2) ∧
    InKingHalfPlane (0, 0) (1, 0) .positive (1/2, 1/2) ∧
    ¬ InKingHalfPlane (0, 0) (1, 0) .positive (rayPoint (0, 0) .northEast 0) ∧
    InKingHalfPlane (0, 0) (1, 0) .negative (rayPoint (0, 0) .northEast (-1)) := by
  norm_num [HalfPlaneSide.sign, halfPlaneCross, InKingHalfPlane,
    rayPoint, rayParameter, OnRationalRay, RayDirection.vector]

-- The ray intersection is outside the board, although both origins are on it.
example : OnRationalRay (7, 0) .northEast (10, 3) ∧
    OnRationalRay (7, 6) .southEast (10, 3) ∧
    InKingHalfPlane (7, 0) (7, 6) .negative (10, 3) ∧
    .northEast ∈ halfPlaneDirections (7, 0) (7, 6) .negative ∧
    .southEast ∈ halfPlaneDirections (7, 0) (7, 6) .negative := by
  norm_num [halfPlaneDirections, HalfPlaneSide.sign, rayOffset,
    halfPlaneCross, InKingHalfPlane, rayPoint, rayParameter, OnRationalRay, RayDirection.vector]

-- No extra half-plane assumption is needed at the trace interface. The
-- period hypotheses exclude king-line rays before classifying crossings.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len)
    (p : PlanePoint) (hx : tr.CheckingCrossing (kp 0) p) :
    ∃ side, ∀ c d, OnRationalRay (kp 0 c).toPlane d p →
      d ∈ halfPlaneDirections (kp 0 .white).toPlane (kp 0 .black).toPlane side := by
  obtain ⟨side, hs, _⟩ :=
    tr.checkingCrossing_halfPlane_unique_of_periodic_checks kp hl hk hc hp hn p hx
  exact ⟨side, hs.2⟩

end MPC.Chess.Tests
