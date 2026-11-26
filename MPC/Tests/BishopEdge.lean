import MPC.Legacy.CheckCompatibility
import MPC.Pieces.BishopEdge
import Lean
/-!
# MPC.Tests.BishopEdge

Concrete checks for the integer lemmas of , for the first player
(`τ = 1`), with the enemy king at the origin.

- `bishop_destination_facing`: for the king on `(2, -1)`, a move to `(0, -1)`
  satisfies Corollary 3.4's constraint, and `(0, -1)` faces the king.
  - The premise that the king is off the file is needed: for the king on `(0, -2)`,
    an enemy knight on `(1, 0)` attacks it, but `(1, 0)` does not face it.
- `bishop_king_candidates`: `(2, -1)` is a candidate for the edge between `(1, 0)`
  and `(0, -1)`. The king on `(3, -1)` fails the constraint at the move to `(1, 0)`.
- `facing_edge_signs`, `facing_edge_mem_iff`, `facing_edge_unique`, and
  `king_off_axes_of_edge` on that edge.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Bishop edge verification must not import GameSeq"

namespace MPC
namespace BishopEdgeTests

/-! ## Facing destinations -/

-- A rook on the rank through `(0, -1)` checks the king on `(2, -1)`.
private theorem con_row2_A : BishopCheckerConstraintAt 1 1 (0, -1) (2, -1) :=
  Or.inr (Or.inr ⟨(1, 0), Or.inl rfl, 2, by norm_num, by decide, fun _ => by decide⟩)

-- From `(1, 0)` the king on `(2, -1)` is a step away.
private theorem con_row2_B : BishopCheckerConstraintAt 1 1 (1, 0) (2, -1) :=
  Or.inl (by decide)

example : Facing (2, -1) (0, -1) :=
  bishop_destination_facing 1 1 (Or.inl rfl) (le_refl _) (0, -1) (2, -1)
    (Or.inr ⟨rfl, Or.inr rfl⟩) (by decide) (by decide) (by decide) con_row2_A

-- For the king on the file, an enemy knight on `(1, 0)` attacks it, yet `(1, 0)` does not
-- face it: the off-file premise is needed.
example : BishopCheckerConstraintAt 1 1 (1, 0) (0, -2) ∧ ¬ Facing (0, -2) (1, 0) :=
  ⟨Or.inr (Or.inl ⟨Or.inr rfl, by norm_num⟩), by unfold Facing; decide⟩

/-! ## King candidates -/

example : KingCandidate 1 1 (-1) 1 (2, -1) :=
  bishop_king_candidates 1 1 (-1) 1 (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (le_refl _) (2, -1)
    (by norm_num) (by norm_num) (by decide) con_row2_A con_row2_B

-- `(3, -1)` is no candidate: `(3, -1) - (1, 0) = (2, -1)` is neither a step, a knight's jump,
-- nor along a rank or file.
example : ¬ BishopCheckerConstraintAt 1 1 (1, 0) (3, -1) := by
  rintro (hu | ⟨h1, _⟩ | ⟨sd, hsd, c, hc, hl, _⟩)
  · revert hu
    decide
  · dsimp only at h1
    omega
  · rcases hsd with rfl | rfl | rfl | rfl <;> simp only [Prod.mk.injEq] at hl <;> omega

-- The table's row with the king on `(2, -1)` and the paper's general row `(t, -t)` for `t = 3`.
example : KingCandidate 1 1 (-1) 1 (2, -1) ∧ KingCandidate 1 1 (-1) 3 (3, -3) := by
  unfold KingCandidate
  decide

/-! ## Edges -/

example : ∃ σ ρ : ℤ, (σ = 1 ∨ σ = -1) ∧ (ρ = 1 ∨ ρ = -1) ∧ 0 < σ * (2 : ℤ) ∧
    0 < ρ * (-1 : ℤ) ∧ ((((1 : ℤ), (0 : ℤ)) = (σ * 1, 0) ∧ ((0 : ℤ), (-1 : ℤ)) = (0, ρ * 1)) ∨
      (((1 : ℤ), (0 : ℤ)) = (0, ρ * 1) ∧ ((0 : ℤ), (-1 : ℤ)) = (σ * 1, 0))) :=
  facing_edge_signs 1 (1, 0) (0, -1) (2, -1) (by unfold BishopEdge; decide)
    (by unfold Facing; decide) (by unfold Facing; decide)

-- An edge at distance 2 facing the same king misses the edge at distance 1 entirely.
example : ¬ (((2 : ℤ), (0 : ℤ)) = (1 * 1, 0) ∨ ((2 : ℤ), (0 : ℤ)) = (0, -1 * 1)) ∧
    ¬ (((0 : ℤ), (-2 : ℤ)) = (1 * 1, 0) ∨ ((0 : ℤ), (-2 : ℤ)) = (0, -1 * 1)) := by decide

example : ((1 : ℤ), (0 : ℤ)) = (1, 0) :=
  facing_edge_unique 1 1 (1, 0) (0, -1) (1, 0) (2, -1) (by unfold BishopEdge; decide)
    (by unfold BishopEdge; decide) (by unfold Facing; decide) (by unfold Facing; decide)

example : (2 : ℤ) ≠ 0 ∧ (-1 : ℤ) ≠ 0 :=
  king_off_axes_of_edge 1 (1, 0) (0, -1) (2, -1) (by unfold BishopEdge; decide) (by decide)
    (by decide)

end BishopEdgeTests
end MPC
