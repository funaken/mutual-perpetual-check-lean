import MPC.Geometry.Lattice
/-!
# MPC.Geometry.Line

直線・線分・共線性の定義。
定義3.1: 睨むライン = 駒の位置と相手玉の位置を結ぶ線分。
-/

namespace MPC.Geometry

/-- 3点が一直線上にあるか -/
def collinear (a b c : Point) : Prop :=
  (b.1 - a.1) * (c.2 - a.2) = (c.1 - a.1) * (b.2 - a.2)

/-- 点 p が線分 ab 上にあるか（端点含む）-/
def onSegment (a b p : Point) : Prop :=
  collinear a b p ∧
  min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 ∧
  min a.2 b.2 ≤ p.2 ∧ p.2 ≤ max a.2 b.2

/-- 点 p が線分 ab の内部にあるか（端点を含まない）-/
def onSegmentInterior (a b p : Point) : Prop :=
  onSegment a b p ∧ p ≠ a ∧ p ≠ b

end MPC.Geometry
