import MPC.Basic.Defs
/-!
# MPC.Basic.Grid

9x9 盤面の格子点に関する基本的な性質。
位置の整数変換と、方向に沿った移動のユーティリティ。
-/

namespace MPC

/-- 整数座標が盤面内 (0..8, 0..8) にあるか -/
def onBoard (p : ℤ × ℤ) : Prop := 0 ≤ p.1 ∧ p.1 < 9 ∧ 0 ≤ p.2 ∧ p.2 < 9

/-- 整数座標から Pos への変換（盤面内である証拠が必要）-/
noncomputable def toPos (p : ℤ × ℤ) (_h : onBoard p) : Pos :=
  (⟨p.1.toNat, by simp [onBoard] at _h; omega⟩, ⟨p.2.toNat, by simp [onBoard] at _h; omega⟩)

/-- Pos に方向ベクトルを加算し、盤面内なら Some を返す -/
def Pos.addDir (p : Pos) (d : Dir) : Option (ℤ × ℤ) :=
  let q : ℤ × ℤ := (↑p.1.val + d.1, ↑p.2.val + d.2)
  if 0 ≤ q.1 ∧ q.1 < 9 ∧ 0 ≤ q.2 ∧ q.2 < 9 then some q else none

/-- 2つの Pos 間の方向ベクトル -/
def Pos.dirTo (src dst : Pos) : Dir :=
  (↑dst.1.val - ↑src.1.val, ↑dst.2.val - ↑src.2.val)

/-- 方向ベクトルを正規化（各成分を -1, 0, 1 に）-/
def Dir.normalize (d : Dir) : Dir :=
  (Int.sign d.1, Int.sign d.2)

/-- 2点間が直線上（縦・横・斜め）かどうか -/
def Pos.isAligned (a b : Pos) : Prop :=
  let d := a.dirTo b
  d = (0, 0) ∨ d.1 = 0 ∨ d.2 = 0 ∨ d.1.natAbs = d.2.natAbs

end MPC
