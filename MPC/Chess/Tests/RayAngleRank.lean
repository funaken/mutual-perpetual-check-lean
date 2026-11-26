import MPC.Chess.RayAngleRank

namespace MPC.Chess.Tests

-- Figure 3 (upper left): kings at (0,0) and (3,1). Upper side from K: NE, N, NW, W
-- have ranks 1–4; from L the order is W, NW, N, NE.
example : kingRayRank (0, 0) (3, 1) .northEast = 1 ∧ kingRayRank (0, 0) (3, 1) .north = 2 ∧
    kingRayRank (0, 0) (3, 1) .northWest = 3 ∧ kingRayRank (0, 0) (3, 1) .west = 4 ∧
    kingRayRank (3, 1) (0, 0) .west = 1 ∧ kingRayRank (3, 1) (0, 0) .northWest = 2 ∧
    kingRayRank (3, 1) (0, 0) .north = 3 ∧ kingRayRank (3, 1) (0, 0) .northEast = 4 := by
  norm_num [kingRayRank, angleRank, rayOffset, rayDot, RayDirection.vector]

-- The lower side uses the same bins with the other orientation.
example : kingRayRank (0, 0) (3, 1) .east = 1 ∧ kingRayRank (0, 0) (3, 1) .southEast = 2 ∧
    kingRayRank (3, 1) (0, 0) .southWest = 1 ∧ kingRayRank (3, 1) (0, 0) .south = 2 ∧
    .east ∈ halfPlaneDirections (0, 0) (3, 1) .negative ∧
    .south ∈ halfPlaneDirections (0, 0) (3, 1) .negative := by
  norm_num [kingRayRank, angleRank, rayOffset, rayDot, RayDirection.vector,
    halfPlaneDirections, HalfPlaneSide.sign]

-- Axis and diagonal kings: an exact 45° angle is in the first, closed bin, and
-- only three directions are ranked on each side.
example : kingRayRank (0, 0) (4, 0) .northEast = 1 ∧ kingRayRank (0, 0) (4, 0) .north = 2 ∧
    kingRayRank (0, 0) (4, 0) .northWest = 3 ∧ kingRayRank (4, 0) (0, 0) .north = 2 ∧
    kingRayRank (0, 0) (3, 3) .north = 1 ∧ kingRayRank (0, 0) (3, 3) .northWest = 2 ∧
    kingRayRank (0, 0) (3, 3) .west = 3 ∧ kingRayRank (3, 3) (0, 0) .northWest = 2 := by
  norm_num [kingRayRank, angleRank, rayOffset, rayDot, RayDirection.vector]

-- Exchanging the kings reverses the side of each direction.
example : .north ∈ halfPlaneDirections (0, 0) (3, 1) .positive ∧
    .north ∈ halfPlaneDirections (3, 1) (0, 0) .negative :=
  ⟨by norm_num [halfPlaneDirections, HalfPlaneSide.sign, rayOffset, RayDirection.vector],
    (mem_halfPlaneDirections_swap (0, 0) (3, 1) .positive .north).mpr
      (by norm_num [halfPlaneDirections, HalfPlaneSide.sign, rayOffset, RayDirection.vector])⟩

-- The bound is attained: rank 1 from L meets rank 3 from K at (-1, 1), off the board.
example : OnRationalRay (0, 0) .northWest (-1, 1) ∧ OnRationalRay (3, 1) .west (-1, 1) ∧
    kingRayRank (0, 0) (3, 1) .northWest + kingRayRank (3, 1) (0, 0) .west = 4 := by
  norm_num [OnRationalRay, rayParameter, rayPoint, kingRayRank, angleRank, rayOffset, rayDot,
    RayDirection.vector]

-- A rank-4 ray meets no nonparallel ray, and a rank-3 ray meets only rank-1 rays.
example {o r p : PlanePoint} {d e : RayDirection} (hd : OnRationalRay o d p)
    (he : OnRationalRay r e p) (ho : p ≠ o) (hr : p ≠ r) (hde : rayDet d e ≠ 0) :
    kingRayRank o r d ≠ 4 ∧ (kingRayRank o r d = 3 → kingRayRank r o e = 1) := by
  have := kingRayRank_add_le_four hd he ho hr hde
  have := kingRayRank_pos r o e
  omega

-- The nonparallel premise is needed: overlapping parallel rays from both kings
-- can have ranks 4 and 1.
example : OnRationalRay (0, 0) .west (-1, 0) ∧ OnRationalRay (4, 0) .west (-1, 0) ∧
    rayDet .west .west = 0 ∧
    kingRayRank (0, 0) (4, 0) .west + kingRayRank (4, 0) (0, 0) .west = 5 := by
  norm_num [OnRationalRay, rayParameter, rayPoint, kingRayRank, angleRank, rayOffset, rayDot,
    rayDet, RayDirection.vector]

-- Distinct directions on one side never share a rank.
example (o r : PlanePoint) (side : HalfPlaneSide) (d e : RayDirection)
    (hd : d ∈ halfPlaneDirections o r side) (he : e ∈ halfPlaneDirections o r side)
    (h : kingRayRank o r d = kingRayRank o r e) : d = e :=
  kingRayRank_injOn o r side (Finset.mem_coe.mpr hd) (Finset.mem_coe.mpr he) h

end MPC.Chess.Tests
