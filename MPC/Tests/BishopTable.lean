import MPC.Pieces.BishopTable
import Lean
/-!
# MPC.Tests.BishopTable

Concrete checks for , for the first player (`τ = 1`, so `ρ = -1`) and
`σ = 1`, with the enemy king at the origin.

- `bishop_table_cases` classifies the paper's row with the king on `(2, -1)` as a row
  of Table 1 (`BishopRow`). The king on `(3, -3)` with `t = t' = 3` is no row: both
  bishops would use the same squares `(3, 0)` and `(0, -3)`.
- The shared-square case `t = 1`, `t' = 2` with the king on `(1, -2)`: the
  opponent's squares are `(-1, -2)` and `(1, 0)`. Its diagonal move from `(-1, -2)`
  into `(1, 0)` passes `(0, -1)`, `o`'s other square.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Bishop table verification must not import GameSeq"

namespace MPC
namespace BishopTableTests

-- The paper's row with the king on `(2, -1)`.
example : (-1 : ℤ) = -1 ∧ (BishopRow 1 (-1) 1 1 (2, -1) ∨ ((1 : ℤ) = 1 ∧ ((2 : ℤ), (-1 : ℤ)) =
    (1 * 1, -1 * 1)) ∨ (((2 : ℤ), (-1 : ℤ)) = (1, 2 * -1) ∧
      (((1 : ℤ) = 1 ∧ (1 : ℤ) = 2) ∨ ((1 : ℤ) = 2 ∧ (1 : ℤ) = 1)))) :=
  bishop_table_cases 1 1 (-1) 1 1 (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (le_refl _) (2, -1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    (by unfold KingCandidate; decide) (by unfold KingCandidate; decide)

example : BishopRow 1 (-1) 1 1 (2, -1) ∧ ¬ BishopRow 1 (-1) 3 3 (3, -3) := by
  unfold BishopRow
  decide

-- The shared-square case: the opponent's move `(-1, -2) → (1, 0)` passes `(0, -1)`.
example : ((1 : ℤ), (0 : ℤ)) = (-1 + 2 * 1, -2 + 2 * 1) ∧
    ((0 : ℤ), (-1 : ℤ)) = (-1 + 1 * 1, -2 + 1 * 1) := by decide

end BishopTableTests
end MPC
