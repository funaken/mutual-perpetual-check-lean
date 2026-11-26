import MPC.Legacy.CheckCompatibility
import MPC.Pieces.GoldTypeMove
import Lean
/-!
# MPC.Tests.GoldTypeMove

Concrete checks for the gold-type case analysis of .

- The two forward moves the case analysis allows, for the first player:
  `(1, 1) → (0, 2)` (the paper's) and `(2, 0) → (1, 1)`. Their mirror images for
  the second player go forward too.
- Each premise of `gold_step_forward` is needed. Each move below satisfies every
  other premise and does not go forward:
  - `(0, 1) → (1, 1)` sideways: the gold on `(0, 1)` attacks the king.
  - `(1, 1) → (1, 0)` backwards: the gold on `(1, 0)` attacks the king.
  - `(0, 3) → (0, 2)` backwards: both ends are on one line through the king.
  - `(2, 1) → (1, 1)` sideways: `(2, 1)` is on no line through the king.
- In board coordinates (`forwardRank_lt_of_gold_step_between_rays`), with the enemy
  king at `(4, 4)`: a sente gold on `(5, 5)` stepping to `(4, 6)` gains a rank.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Gold-type move verification must not import GameSeq"

namespace MPC
namespace GoldTypeMoveTests

/-! ## The case analysis -/

-- The paper's move and the second forward move, for both players.
example : 0 < forwardSign .sente * (2 - 1) ∧ 0 < forwardSign .sente * (1 - 0) ∧
    0 < forwardSign .gote * (-2 - -1) := by
  refine ⟨gold_step_forward .sente (1, 1) (0, 2) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    gold_step_forward .sente (2, 0) (1, 1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    gold_step_forward .gote (1, -1) (0, -2) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

-- Without the non-attack premise at the source: a sideways move.
example : (((0 : ℤ), (1 : ℤ)) : ℤ × ℤ).1 = 0 ∧ (((1 : ℤ), (1 : ℤ)) : ℤ × ℤ).1 = (1 : ℤ) ∧
    (0 : ℤ) * 1 - 1 * 1 ≠ 0 ∧
    ((1 - 0, 1 - 1) : Dir) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ((-0, -1) : Dir) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ((-1, -1) : Dir) ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ¬ 0 < forwardSign .sente * (1 - 1) := by decide

-- Without the non-attack premise at the destination: a backward move.
example : (1 : ℤ) * 0 - 1 * 1 ≠ 0 ∧
    ((1 - 1, 0 - 1) : Dir) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ((-1, -1) : Dir) ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ((-1, -0) : Dir) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ¬ 0 < forwardSign .sente * (0 - 1) := by decide

-- Without non-collinearity: both ends on one line, neither attacking the king.
example : (0 : ℤ) * 2 - 3 * 0 = 0 ∧
    ((0 - 0, 2 - 3) : Dir) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ((-0, -3) : Dir) ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ((-0, -2) : Dir) ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ¬ 0 < forwardSign .sente * (2 - 3) := by decide

-- Without the line premise: `(2, 1)` lies on no line through the king.
example : ¬ ((2 : ℤ) = 0 ∨ (1 : ℤ) = 0 ∨ (2 : ℤ) = 1 ∨ (2 : ℤ) = -1) ∧
    (2 : ℤ) * 1 - 1 * 1 ≠ 0 ∧
    ((1 - 2, 1 - 1) : Dir) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ((-2, -1) : Dir) ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ((-1, -1) : Dir) ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente) ∧
    ¬ 0 < forwardSign .sente * (1 - 1) := by decide

/-! ## Board coordinates -/

private def K : Pos := (4, 4)

-- A sente gold on `(5, 5)`, diagonally in front of the king, steps to `(4, 6)`.
example : forwardRank .sente ((5, 5) : Pos) < forwardRank .sente ((4, 6) : Pos) :=
  forwardRank_lt_of_gold_step_between_rays .sente K (5, 5) (4, 6) (1, 1) (0, 1) 1 2
    (by unfold OnRay K; decide) (by unfold OnRay K; decide) (by decide) (by decide)
    (by decide) (by unfold K; decide) (by unfold K; decide)

-- The two half-lines are not collinear with the king.
example : ((Pos.toInt (5, 5)).1 - K.toInt.1) * ((Pos.toInt (4, 6)).2 - K.toInt.2) -
    ((Pos.toInt (5, 5)).2 - K.toInt.2) * ((Pos.toInt (4, 6)).1 - K.toInt.1) ≠ 0 :=
  OnRay.cross_ne_zero (K := K) (P := (5, 5)) (Q := (4, 6)) (d := (1, 1)) (e := (0, 1)) (a := 1)
    (b := 2) (by unfold OnRay K; decide) (by unfold OnRay K; decide) (by decide) (by decide)

end GoldTypeMoveTests
end MPC
