import MPC.Geometry.AngleKey
import Lean
/-!
# MPC.Tests.AngleKey

Concrete checks for . The enemy king `K` is on `(4, 1)` and the own king
`L` on `(4, 7)`, so `v = L - K = (0, 6)` and `|v|² = 36`.

- Keys increase with the angle: the squares `(4, 3)`, `(2, 3)`, `(2, 1)` and
  `(3, 0)` make 0°, 45°, 90° and 135° at `K`, and their keys are `-36`, `-18`, `0`
  and `18`.
- `angleKey_eq_of_ray`: `(2, 3)` is one of three steps of `(1, -1)` from `(1, 4)`
  to `K`, so both squares have the key `-18`.
- `angleKey_lt_of_between`: a piece on `(1, 4)` reaches `L` in three steps of
  `(1, 1)`; the square `(2, 5)` between them has the smaller key `-144/5`.
- The premise `lineSide K L Q ≠ 0` is needed: on the kings' line, `(4, 5)` lies
  between `(4, 3)` and `L` and has the same key `-36`.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Angle key verification must not import GameSeq"

namespace MPC
namespace AngleKeyTests

/-- The enemy king. -/
abbrev K : Pos := (4, 1)
/-- The own king. -/
abbrev L : Pos := (4, 7)

/-! ## Keys increase with the angle -/

example : angleKey K L (4, 3) = -36 := by
  norm_num [angleKey, vecKey, Pos.toInt, Fin.coe_ofNat_eq_mod]
example : angleKey K L (2, 3) = -18 := by
  norm_num [angleKey, vecKey, Pos.toInt, Fin.coe_ofNat_eq_mod]
example : angleKey K L (2, 1) = 0 := by
  norm_num [angleKey, vecKey, Pos.toInt, Fin.coe_ofNat_eq_mod]
example : angleKey K L (3, 0) = 18 := by
  norm_num [angleKey, vecKey, Pos.toInt, Fin.coe_ofNat_eq_mod]

/-! ## One half-line from the enemy king -/

example : angleKey K L (2, 3) = angleKey K L (1, 4) :=
  angleKey_eq_of_ray K L (1, 4) (2, 3) (1, -1) 1 3 (by norm_num) (by norm_num)
    (by decide) (by decide)

example : angleKey K L (1, 4) = -18 := by
  norm_num [angleKey, vecKey, Pos.toInt, Fin.coe_ofNat_eq_mod]

/-! ## An interposition lowers the angle -/

example : angleKey K L (2, 5) < angleKey K L (1, 4) :=
  angleKey_lt_of_between K L (1, 4) (2, 5) (1, 1) 1 3 (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide)

example : angleKey K L (2, 5) = -144 / 5 := by
  norm_num [angleKey, vecKey, Pos.toInt, Fin.coe_ofNat_eq_mod]

/-! ## Off the kings' line is needed -/

example : lineSide K L (4, 3) = 0 := by decide

example : angleKey K L (4, 5) = angleKey K L (4, 3) := by
  norm_num [angleKey, vecKey, Pos.toInt, Fin.coe_ofNat_eq_mod]

end AngleKeyTests
end MPC
