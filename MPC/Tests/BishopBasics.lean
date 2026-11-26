import MPC.Pieces.BishopBasics
import Lean
/-!
# MPC.Tests.BishopBasics

Concrete checks for the board lemmas of .

- Bishops and horses slide diagonally (`diag_of_bishopHorse_slideDir`), and horses
  step one square along a rank or file (`orth_of_bishopHorse_stepDir`). Both
  premises are needed: a rook slides along a file, and a dragon steps diagonally.
- The four rank and file unit directions (`orth_unit_cases`).
- A diagonal slide from `(2, 0)` to `(0, -2)` relative to the king keeps the
  distance (`bishopEdge_of_diag_move`). From `(2, 0)` to `(0, -1)` no diagonal slide
  is possible, so the distance must be kept.
- A horse's one-square step does not join `(1, 0)` and `(0, 1)`
  (`not_orth_step_between_rays`).

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Bishop basics verification must not import GameSeq"

namespace MPC
namespace BishopBasicsTests

/-! ## Directions -/

example : (((1 : ℤ) = 1 ∨ (1 : ℤ) = -1) ∧ ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1)) ∧
    (((0 : ℤ) = 0 ∧ ((1 : ℤ) = 1 ∨ (1 : ℤ) = -1)) ∨ ((1 : ℤ) = 0 ∧ ((0 : ℤ) = 1 ∨ (0 : ℤ) = -1))) :=
  ⟨diag_of_bishopHorse_slideDir .horse .gote (1, -1) (Or.inr rfl) (by decide),
    orth_of_bishopHorse_stepDir .horse .sente (0, 1) (Or.inr rfl) (by decide)⟩

-- Without the kind premise: a rook slides along a file, a dragon steps diagonally.
example : ((0, 1) : Dir) ∈ PieceType.rook.slideDirs.map (Dir.forPlayer · .sente) ∧
    ((1, 1) : Dir) ∈ PieceType.dragon.stepDirs.map (Dir.forPlayer · .sente) := by decide

example (e : Dir) (hu : e ∈ PieceType.king.stepDirs) (h : e.1 = 0) :
    e = (0, 1) ∨ e = (0, -1) := by
  rcases orth_unit_cases hu (Or.inl h) with rfl | rfl | rfl | rfl
  · simp at h
  · simp at h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## Moves between a rank and a file -/

-- `(2, 0) → (0, -2)`: a diagonal slide of two squares keeps the distance.
example : BishopEdge 2 (2 * 1, 2 * 0) (2 * 0, 2 * -1) :=
  bishopEdge_of_diag_move (1, 0) (0, -1) 2 2 (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide) (by decide) (-1) (-1) 2 (Or.inr rfl) (Or.inr rfl) (by norm_num)
    (by norm_num) (by norm_num)

-- `(2, 0) → (0, -1)` is no diagonal slide: its displacement `(-2, -1)` is not.
example : ¬ ∃ k : ℤ, 1 ≤ k ∧ ((-2 : ℤ) = k * 1 ∨ (-2 : ℤ) = k * -1) ∧
    ((-1 : ℤ) = k * 1 ∨ (-1 : ℤ) = k * -1) := by
  rintro ⟨k, hk, h1, h2⟩
  omega

-- A one-square step along a rank or file does not join `(1, 0)` and `(0, 1)`.
example : ¬ (((1 : ℤ) * 0 - 1 * 1 = 0 ∧ ((1 : ℤ) * 1 - 1 * 0 = 1 ∨ (1 : ℤ) * 1 - 1 * 0 = -1)) ∨
    ((1 : ℤ) * 1 - 1 * 0 = 0 ∧ ((1 : ℤ) * 0 - 1 * 1 = 1 ∨ (1 : ℤ) * 0 - 1 * 1 = -1))) :=
  fun h => not_orth_step_between_rays (1, 0) (0, 1) 1 1 (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide) (by decide) h

end BishopBasicsTests
end MPC
