import MPC.Geometry.Line
/-!
# MPC.Legacy.Angle

2D整数ベクトルの外積と角度関連の定義。
定義4.2の角 ∠AKL と定義4.3の増減 (ang, iang, dang) は、手順モデルでは
`MPC/Basic/AngleKey.lean` の `angleKey` と `MPC/Basic/AnglePotential.lean` で扱う。
-/

namespace MPC.Geometry

/-- 2D ベクトルの外積（符号付き面積の2倍に相当） -/
def cross (u v : Point) : ℤ := u.1 * v.2 - u.2 * v.1

/-- 点 p から点 q への方向ベクトル -/
def dirVec (p q : Point) : Point := (q.1 - p.1, q.2 - p.2)

/-- 3点 A, K, L に対する ∠AKL の向き。
    K を中心として KL 方向から KA 方向への回転の符号。
    正 = 反時計回り、負 = 時計回り、0 = 同一直線上。 -/
def angleSign (a k l : Point) : ℤ :=
  Int.sign (cross (dirVec k l) (dirVec k a))

/-- 外積の符号が同じ = 同じ半平面にある -/
def sameSide (k l p q : Point) : Prop :=
  cross (dirVec k l) (dirVec k p) * cross (dirVec k l) (dirVec k q) > 0

/-- 外積が 0 = 直線 KL 上にある -/
def onLine (k l p : Point) : Prop :=
  cross (dirVec k l) (dirVec k p) = 0

end MPC.Geometry
