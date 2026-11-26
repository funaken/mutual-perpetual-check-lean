import MPC.Legacy.CheckCompatibility
import MPC.Pieces.SilverMove
import Lean
/-!
# MPC.Tests.SilverMove

Concrete checks for the silver case analysis of .

- The paper's moves between `(1, 0)` and `(0, 1)` for the first player, and the
  mirrored move from `(-1, 0)` to `(0, -1)` for the second player, satisfy
  `SilverSquares` through `silver_step_between_lines`.
- Each premise of `silver_step_between_lines` is needed. Each silver step below
  satisfies every other premise and is not between `(σ, 0)` and `(0, τ)`:
  - `(-3, -1) → (-3, 0)`: the source is on no line through the king;
  - `(-3, -3) → (-3, -2)`: the destination is on no line through the king;
  - `(-3, -3) → (-4, -4)`: both ends are on one line through the king;
  - `(-1, -1) → (-1, 0)`: the silver on `(-1, -1)` attacks the king;
  - `(-2, 0) → (-1, 1)`: the silver on `(-1, 1)` attacks the king.
- `relTo` and `relTo_inj` on concrete squares.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Silver move verification must not import GameSeq"

namespace MPC
namespace SilverMoveTests

/-! ## The case analysis -/

example : SilverSquares .sente (1, 0) (0, 1) ∧ SilverSquares .sente (0, 1) (1, 0) ∧
    SilverSquares .gote (-1, 0) (0, -1) :=
  ⟨silver_step_between_lines .sente (1, 0) (0, 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    silver_step_between_lines .sente (0, 1) (1, 0) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    silver_step_between_lines .gote (-1, 0) (0, -1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)⟩

private def silverSteps : List Dir := PieceType.silver.stepDirs.map (Dir.forPlayer · .sente)

-- The source is on no line through the king.
example : ¬ ((-3 : ℤ) = 0 ∨ (-1 : ℤ) = 0 ∨ (-3 : ℤ) = -1 ∨ (-3 : ℤ) = -(-1)) ∧
    ((-3 : ℤ) = 0 ∨ (0 : ℤ) = 0 ∨ (-3 : ℤ) = 0 ∨ (-3 : ℤ) = -0) ∧
    (-3 : ℤ) * 0 - (-1) * (-3) ≠ 0 ∧ ((-3 - -3, 0 - -1) : Dir) ∈ silverSteps ∧
    ((3, 1) : Dir) ∉ silverSteps ∧ ((3, 0) : Dir) ∉ silverSteps ∧
    ¬ SilverSquares .sente (-3, -1) (-3, 0) := by
  unfold silverSteps SilverSquares forwardSign
  decide

-- The destination is on no line through the king.
example : ((-3 : ℤ) = 0 ∨ (-3 : ℤ) = 0 ∨ (-3 : ℤ) = -3 ∨ (-3 : ℤ) = -(-3)) ∧
    ¬ ((-3 : ℤ) = 0 ∨ (-2 : ℤ) = 0 ∨ (-3 : ℤ) = -2 ∨ (-3 : ℤ) = -(-2)) ∧
    (-3 : ℤ) * (-2) - (-3) * (-3) ≠ 0 ∧ ((-3 - -3, -2 - -3) : Dir) ∈ silverSteps ∧
    ((3, 3) : Dir) ∉ silverSteps ∧ ((3, 2) : Dir) ∉ silverSteps ∧
    ¬ SilverSquares .sente (-3, -3) (-3, -2) := by
  unfold silverSteps SilverSquares forwardSign
  decide

-- Both ends are on one line through the king.
example : (-3 : ℤ) * (-4) - (-3) * (-4) = 0 ∧ ((-4 - -3, -4 - -3) : Dir) ∈ silverSteps ∧
    ((3, 3) : Dir) ∉ silverSteps ∧ ((4, 4) : Dir) ∉ silverSteps ∧
    ¬ SilverSquares .sente (-3, -3) (-4, -4) := by
  unfold silverSteps SilverSquares forwardSign
  decide

-- The silver on the source attacks the king.
example : (-1 : ℤ) * 0 - (-1) * (-1) ≠ 0 ∧ ((-1 - -1, 0 - -1) : Dir) ∈ silverSteps ∧
    ((1, 1) : Dir) ∈ silverSteps ∧ ((1, 0) : Dir) ∉ silverSteps ∧
    ¬ SilverSquares .sente (-1, -1) (-1, 0) := by
  unfold silverSteps SilverSquares forwardSign
  decide

-- The silver on the destination attacks the king.
example : (-2 : ℤ) * 1 - 0 * (-1) ≠ 0 ∧ ((-1 - -2, 1 - 0) : Dir) ∈ silverSteps ∧
    ((2, 0) : Dir) ∉ silverSteps ∧ ((1, -1) : Dir) ∈ silverSteps ∧
    ¬ SilverSquares .sente (-2, 0) (-1, 1) := by
  unfold silverSteps SilverSquares forwardSign
  decide

/-! ## Relative coordinates -/

example : relTo ((4, 4) : Pos) ((5, 4) : Pos) = (1, 0) ∧
    relTo ((4, 4) : Pos) ((4, 3) : Pos) = (0, -1) := by
  unfold relTo Pos.toInt
  decide

example (q : Pos) (h : relTo ((4, 4) : Pos) q = (1, 0)) : q = (5, 4) :=
  relTo_inj (h.trans (by unfold relTo Pos.toInt; decide))

end SilverMoveTests
end MPC
