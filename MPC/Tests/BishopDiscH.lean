import MPC.Pieces.BishopDiscH
import Lean
/-!
# MPC.Tests.BishopDiscH

Concrete checks for the integer and board facts of .

- `lineSide_eq_cross`: with the first player's king on `(6, 3)` and the second
  player's on `(4, 4)`, the side of `(5, 4)` in both kings' coordinates.
- `not_step_of_multiple`: two steps along `(1, -1)` are neither a king step nor a
  knight's jump; one step is a king step, so the factor two is needed.
- Table 1's row with `o`'s king on `(2, -1)` relative to `K` (`σ = 1`, `τ = 1`): with
  `s = -1`, `X = (1, 0)` and `Y = (2, 0)` lie on side `s`, `X' = (0, -1)` and
  `Y' = (1, -1)` off it. `X` lies between `Y` and `K` on the half-line along
  `(1, 0)`, and `Y'` between `X'` and `L` on the half-line along `(-1, 0)`
  (`OnRay.of_relTo_sub`).

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Bishop disc H verification must not import GameSeq"

namespace MPC
namespace BishopDiscHTests

private def kps : Player → Pos := fun o => if o = .sente then (6, 3) else (4, 4)

example : lineSide (kps .sente) (kps .gote) ((5, 4) : Pos) =
      -forwardSign .sente * ((relTo (kps Player.sente.opponent) (kps .sente)).1 *
        (relTo (kps Player.sente.opponent) ((5, 4) : Pos)).2 -
        (relTo (kps Player.sente.opponent) (kps .sente)).2 *
        (relTo (kps Player.sente.opponent) ((5, 4) : Pos)).1) :=
  lineSide_eq_cross kps .sente (5, 4)

example : ¬ (((2 : ℤ) * 1, (2 : ℤ) * -1) ∈ PieceType.king.stepDirs ∨
    (((2 : ℤ) * 1 = 1 ∨ (2 : ℤ) * 1 = -1) ∧ (2 : ℤ) * -1 = 2 * forwardSign .sente)) :=
  not_step_of_multiple (1, -1) (by decide) 2 (le_refl _) _ rfl .sente

example : ((1 : ℤ) * 1, (1 : ℤ) * -1) ∈ PieceType.king.stepDirs := by decide

-- The row with `o`'s king on `(2, -1)`: the side signs with `s = -1`.
example : let l : ℤ × ℤ := (2, -1)
    let side := fun v : ℤ × ℤ => (-1 : ℤ) * (-1 * (l.1 * v.2 - l.2 * v.1))
    0 < side (1, 0) ∧ 0 < side (2, 0) ∧ ¬ 0 < side (0, -1) ∧ ¬ 0 < side (1, -1) := by decide

private def K : Pos := (4, 4)
private def L : Pos := (6, 3)

example : OnRay K (1, 0) 1 ((5, 4) : Pos) ∧ OnRay K (1, 0) 2 ((6, 4) : Pos) ∧
    OnRay L (-1, 0) 1 ((5, 3) : Pos) ∧ OnRay L (-1, 0) 2 ((4, 3) : Pos) := by
  refine ⟨by unfold OnRay K; decide, by unfold OnRay K; decide,
    OnRay.of_relTo_sub (K := K) (by decide) one_pos (by unfold relTo K L Pos.toInt; decide),
    OnRay.of_relTo_sub (K := K) (by decide) two_pos (by unfold relTo K L Pos.toInt; decide)⟩

end BishopDiscHTests
end MPC
