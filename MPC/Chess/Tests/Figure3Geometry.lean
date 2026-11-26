import MPC.Chess.Figure3Geometry

namespace MPC.Chess.Tests

open LatticeFrame

private def identityFrame : LatticeFrame := ⟨false, false, false⟩

-- The three shapes of the upper row of Figure 3 have all four crossings on the
-- board: `(b, b)`, `((a+b)/2, (a+b)/2)`, `(0, b)` and `(0, a+b)` from `K = (0, 0)`.
example : OnRay (0, 0) .northEast (1, 1) ∧ OnRay (3, 1) .west (1, 1) ∧
    OnRay (0, 0) .northEast (2, 2) ∧ OnRay (3, 1) .northWest (2, 2) ∧
    OnRay (0, 0) .north (0, 1) ∧ OnRay (3, 1) .west (0, 1) ∧
    OnRay (0, 0) .north (0, 4) ∧ OnRay (3, 1) .northWest (0, 4) := by decide

example : OnRay (0, 0) .northEast (3, 3) ∧ OnRay (5, 1) .northWest (3, 3) ∧
    OnRay (0, 0) .north (0, 6) ∧ OnRay (5, 1) .northWest (0, 6) ∧
    OnRay (0, 0) .northEast (3, 3) ∧ OnRay (4, 2) .northWest (3, 3) ∧
    OnRay (0, 0) .north (0, 6) ∧ OnRay (4, 2) .northWest (0, 6) := by decide

-- Kings on an axis: the two rank-2 rays are parallel and never meet.
example : ¬ ∃ q : Pos, OnRay (0, 0) .north q ∧ OnRay (2, 0) .north q := by decide

-- Kings on a diagonal: the two rank-2 rays are the same direction.
example : ¬ ∃ q : Pos, OnRay (0, 0) .northWest q ∧ OnRay (2, 2) .northWest q := by decide

-- `a + b` odd: the crossing `((a+b)/2, (a+b)/2)` is not a lattice point.
example : ¬ ∃ q : Pos, OnRay (0, 0) .northEast q ∧ OnRay (4, 1) .northWest q := by decide

-- `a + b = 8`: the crossing `(0, a+b)` is beyond the board.
example : ¬ ∃ q : Pos, OnRay (0, 0) .north q ∧ OnRay (6, 2) .northWest q := by decide

-- Board squares differ by at most seven in every canonical coordinate.
example (p q : Pos) (F : LatticeFrame) (v : PlanePoint)
    (h : q.toPlane = p.toPlane + F.apply v) : |v.1| ≤ 7 ∧ |v.2| ≤ 7 :=
  abs_le_seven_of_frame h

-- Canonical coordinates exist for every pair of distinct kings; for the mirror
-- image of Figure 3 the frame is a reflection.
example : ∃ (F : LatticeFrame) (a b : ℤ), 0 ≤ b ∧ b ≤ a ∧ 0 < a ∧
    Pos.toPlane (3, 1) = Pos.toPlane (6, 0) + F.apply ((a : ℚ), (b : ℚ)) :=
  exists_frame_canonical (6, 0) (3, 1) (by decide)

-- With the canonical north on the positive side of the identity frame, the side
-- and the frame orientation agree.
example : HalfPlaneSide.positive.sign * identityFrame.det = 1 := by
  apply side_sign_mul_det_of_north (K := (0, 0)) (L := (3, 1)) (a := 3) (b := 1)
  · norm_num [identityFrame, apply]
  · norm_num
  · norm_num [identityFrame, dir, halfPlaneDirections, HalfPlaneSide.sign, rayOffset,
      RayDirection.vector]

end MPC.Chess.Tests
