import MPC.Geometry.HalfPlaneChecker
import Lean
/-!
# MPC.Tests.HalfPlaneChecker

Concrete checks for the half-plane geometry behind Proposition 3.8.

- With kings at (0,0) and (4,2), the signed area is zero on their line (for
  example at (2,1)), positive on one side, and negative on the other.
- A point strictly between a point and a king lies on that point's side.
- Two unit directions that reach the same point from the same point coincide.

The periodic theorems (no double check, the reply's side, the discovered
checker's side) are not exercised: no periodic mutual-check trace is
constructed. 's verification shows that periodicity is needed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Half-plane checker verification must not import GameSeq"

namespace MPC
namespace HalfPlaneCheckerTests

-- On the line, above it, and below it.
example : lineSide (0, 0) (4, 2) (2, 1) = 0 ∧ 0 < lineSide (0, 0) (4, 2) (1, 3) ∧
    lineSide (0, 0) (4, 2) (3, 0) < 0 := by
  unfold lineSide
  decide

example : Geometry.collinear (Pos.toInt (0, 0)) (Pos.toInt (4, 2)) (Pos.toInt (2, 1)) :=
  (lineSide_eq_zero_iff_collinear _ _ _).mp (by unfold lineSide; decide)

-- (4,4) lies strictly between (4,5) and the king (4,2) along (0,-1), so it is on the
-- same (positive) side as (4,5).
example : 0 < 1 * lineSide (0, 0) (4, 2) (4, 4) ↔ 0 < 1 * lineSide (0, 0) (4, 2) (4, 5) :=
  lineSide_pos_iff_of_between (0, 0) (4, 2) (4, 5) (4, 4) (4, 2) (0, -1) 1 3 1
    (by decide) (by decide) (lineSide_right _ _) (by decide) (by decide)

-- From (1,1), reaching (3,3) in two diagonal steps fixes the direction and count.
example : ((1, 1) : Dir) = (1, 1) ∧ (2 : ℤ) = 2 :=
  same_ray (1, 1) (3, 3) (1, 1) (1, 1) 2 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

end HalfPlaneCheckerTests
end MPC
