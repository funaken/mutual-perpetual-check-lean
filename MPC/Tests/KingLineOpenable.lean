import MPC.Geometry.KingLineOpenable
import Lean
/-!
# MPC.Tests.KingLineOpenable

Concrete checks for the geometry behind Proposition 3.5.

- Swapping the first two points keeps collinearity, and a non-collinear triple
  stays non-collinear.
- Every oriented step direction is a unit step or a knight's jump, so no piece
  steps two squares along a line.
- A point collinear with two points of a file lies on that file.
- A point strictly between two points of a diagonal is on the slide path between
  them, in either order.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed. 's verification shows that periodicity is needed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "King line openable verification must not import GameSeq"

namespace MPC
namespace KingLineOpenableTests

-- (0,0), (2,1), (4,2) are collinear in either order of the first two; (0,0),
-- (2,1), (4,3) are not.
example : Geometry.collinear (2, 1) (0, 0) (4, 2) :=
  (Geometry.collinear_swap _ _ _).mp (by unfold Geometry.collinear; decide)

example : ¬ Geometry.collinear (2, 1) (0, 0) (4, 3) := fun h =>
  absurd ((Geometry.collinear_swap _ _ _).mpr h) (by unfold Geometry.collinear; decide)

-- No piece of either owner steps two squares along a file.
example (pt : PieceType) (o : Player) : ((0, 2) : Dir) ∉ pt.stepDirs.map (Dir.forPlayer · o) := by
  intro h
  rcases stepDir_unit_or_knight pt o _ h with h' | h' <;> simp at h'

-- `A` is two steps up the file from `K`; a collinear `L` lies on the same file.
example : ∃ t : ℤ, Pos.toInt (4, 1) =
    ((Pos.toInt (4, 4)).1 + t * (0 : ℤ), (Pos.toInt (4, 4)).2 + t * 1) :=
  exists_line_param_of_collinear (4, 4) (4, 1) (4, 6) (0, 1) 2 (by decide) (by decide)
    (by decide) (by unfold Geometry.collinear; decide)

-- On the diagonal through (0,0), the point at parameter 3 lies between the points
-- at 1 and 4, in both orders.
example : Pos.toInt (3, 3) ∈ slidePath (1, 1) (4, 4) :=
  mem_slidePath_of_between (0, 0) (1, 1) (4, 4) (3, 3) (1, 1) 1 4 3 (by decide) (by decide)
    (by decide) (by decide) (Or.inl ⟨by decide, by decide⟩)

example : Pos.toInt (3, 3) ∈ slidePath (4, 4) (1, 1) :=
  mem_slidePath_of_between (0, 0) (4, 4) (1, 1) (3, 3) (1, 1) 4 1 3 (by decide) (by decide)
    (by decide) (by decide) (Or.inr ⟨by decide, by decide⟩)

-- The end of a wrapping cyclic interval belongs to it.
example : cyclicBetween (3 : Fin 5) 1 1 := cyclicBetween_self_right _ _

end KingLineOpenableTests
end MPC
