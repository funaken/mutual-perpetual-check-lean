import MPC.Chess.LatticeFrame

namespace MPC.Chess.Tests

open LatticeFrame

/-- A quarter turn counterclockwise: `(x, y) ↦ (-y, x)`. -/
private def quarterTurn : LatticeFrame := ⟨true, true, false⟩

/-- The reflection in the vertical axis: `(x, y) ↦ (-x, y)`. -/
private def mirror : LatticeFrame := ⟨false, true, false⟩

-- Directions turn with the frame; rotations have determinant 1, reflections -1.
example : quarterTurn.dir .north = .west ∧ quarterTurn.dir .northEast = .northWest ∧
    quarterTurn.dir .west = .south ∧ mirror.dir .northEast = .northWest ∧
    mirror.dir .north = .north ∧ quarterTurn.det = 1 ∧ mirror.det = -1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> norm_num [det, quarterTurn, mirror]

example : quarterTurn.apply (3, 1) = (-1, 3) ∧ mirror.apply (3, 1) = (-3, 1) := by
  norm_num [apply, quarterTurn, mirror]

-- The point reflection reverses every direction and displacement, and every
-- frame commutes with reversal.
example (F : LatticeFrame) (d : RayDirection) (v : PlanePoint) :
    F.neg.dir d = (F.dir d).opposite ∧ F.neg.apply v = -F.apply v ∧
      F.dir d.opposite = (F.dir d).opposite :=
  ⟨F.neg_dir d, F.neg_apply v, F.dir_opposite d⟩

-- Board rays follow the frame: the canonical north of `quarterTurn` points west.
example : OnRay (2, 2) (quarterTurn.dir .north) (0, 2) ∧
    ¬ OnRay (2, 2) (quarterTurn.dir .north) (2, 4) := by decide

-- Ranks are computed in canonical coordinates. With `L = K + F(3, 1)` for the
-- quarter turn, the canonical northeast has rank 1 at `K` and the canonical west
-- has rank 1 at `L`, exactly as for kings at `(0,0)` and `(3,1)`.
example : kingRayRank (0, 0) (-1, 3) (quarterTurn.dir .northEast) = 1 ∧
    kingRayRank (0, 0) (-1, 3) (quarterTurn.dir .north) = 2 ∧
    kingRayRank (-1, 3) (0, 0) (quarterTurn.dir .west) = 1 ∧
    kingRayRank (-1, 3) (0, 0) (quarterTurn.dir .northWest) = 2 := by
  have hL : ((-1, 3) : PlanePoint) = (0, 0) + quarterTurn.apply (3, 1) := by
    norm_num [apply, quarterTurn]
  rw [kingRayRank_dir hL, kingRayRank_dir hL, kingRayRank_dir_swap hL, kingRayRank_dir_swap hL]
  norm_num [angleRank, RayDirection.vector]

-- A reflection reverses the side but keeps the rank.
example : mirror.dir .north ∈ halfPlaneDirections (0, 0) (-3, 1) .negative ∧
    .north ∈ halfPlaneDirections (0, 0) (3, 1) .positive ∧
    kingRayRank (0, 0) (-3, 1) (mirror.dir .northEast) = kingRayRank (0, 0) (3, 1) .northEast := by
  norm_num [halfPlaneDirections, HalfPlaneSide.sign, rayOffset, kingRayRank, angleRank, rayDot,
    mirror, dir, RayDirection.reflectX, RayDirection.vector]

-- Reversing a direction moves it to the other side.
example : RayDirection.south ∈ halfPlaneDirections (0, 0) (3, 1) .negative :=
  (mem_halfPlaneDirections_opposite (0, 0) (3, 1) .positive .north).mpr
    (by norm_num [halfPlaneDirections, HalfPlaneSide.sign, rayOffset, RayDirection.vector])

end MPC.Chess.Tests
