import MPC.Geometry.HalfPlaneChecker
import Mathlib.Algebra.Order.Field.Basic
/-!
# MPC.Geometry.AngleKey

A key for the angles of the paper's Definitions 4.2 and 4.3, without
GameSeq.

The paper measures the angle `∠AKL` that a square `A` makes at the enemy king `K`,
from the line to the own king `L`. Its proof of Proposition 4.1 only compares these
angles and adds their differences, so any rational value that is strictly
increasing in the angle serves. `angleKey K L A` is `-(u·v)|u·v| / |u|²` for
`u = A - K` and `v = L - K`, that is `-|v|² cos θ |cos θ|` for the angle `θ`
between `u` and `v`. It needs no square root. It increases strictly with `θ`, but
this file states only the two consequences the proof uses:

- `vecKey_of_mul`: scaling `u` by a positive integer keeps the key, so
  `angleKey_eq_of_ray`: all points of one half-line from `K` have the same key.
- `vecKey_lt_of_comb`: a positive combination of `u` and `v` makes a smaller angle
  with `v` than `u`, unless `u` is parallel to `v`. So `angleKey_lt_of_between`:
  if `L` is `n` steps of `d` from `Q`, every point strictly between them has a
  smaller key than `Q`, unless `Q` is on the line through `K` and `L`. This is the
  geometry of the paper's Remark 4.4: an interposition lowers the angle.

No trace, GameSeq, or axiom is used.
-/

namespace MPC

/-- The key of a vector `u` against a reference vector `v`: `-(u·v)|u·v| / |u|²`,
    that is `-|v|² cos θ |cos θ|` for the angle `θ` between them. The zero vector
    gets the key `0`; callers use squares other than the enemy king's. -/
def vecKey (u v : ℤ × ℤ) : ℚ :=
  -(((u.1 * v.1 + u.2 * v.2) * |u.1 * v.1 + u.2 * v.2| : ℤ) : ℚ) /
    ((u.1 * u.1 + u.2 * u.2 : ℤ) : ℚ)

/-- Definition 4.2's angle `∠AKL` as a key: the square `A` seen from the enemy king
    `K`, against the direction to the own king `L`. -/
def angleKey (K L A : Pos) : ℚ :=
  vecKey (A.toInt.1 - K.toInt.1, A.toInt.2 - K.toInt.2)
    (L.toInt.1 - K.toInt.1, L.toInt.2 - K.toInt.2)

/-- Scaling a vector by a positive integer keeps its key. -/
theorem vecKey_of_mul (a : ℤ) (ha : 0 < a) (u w v : ℤ × ℤ)
    (h1 : w.1 = a * u.1) (h2 : w.2 = a * u.2) : vecKey w v = vecKey u v := by
  have hs : w.1 * v.1 + w.2 * v.2 = a * (u.1 * v.1 + u.2 * v.2) := by
    rw [h1, h2]
    ring
  have hN : (((w.1 * v.1 + w.2 * v.2) * |w.1 * v.1 + w.2 * v.2| : ℤ) : ℚ) =
      (a : ℚ) ^ 2 * (((u.1 * v.1 + u.2 * v.2) * |u.1 * v.1 + u.2 * v.2| : ℤ) : ℚ) := by
    rw [hs, abs_mul, abs_of_pos ha]
    push_cast
    ring
  have hD : ((w.1 * w.1 + w.2 * w.2 : ℤ) : ℚ) =
      (a : ℚ) ^ 2 * ((u.1 * u.1 + u.2 * u.2 : ℤ) : ℚ) := by
    rw [h1, h2]
    push_cast
    ring
  have ha2 : (a : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast ha.ne')
  unfold vecKey
  rw [hN, hD, ← mul_neg, mul_div_mul_left _ _ ha2]

/-- The comparison behind `vecKey_lt_of_comb`, on the integers. With `s = u·v`,
    `t = c·v`, `Q2 = |u|²`, `C2 = |c|²`, `V2 = |v|²` for `c = a u + b v`, the
    identity `t² Q2 - s² C2 = X² (2ab s + b² V2)` (`X` the cross product) decides
    each sign case. -/
private theorem key_lt_abstract (a b s t C2 Q2 V2 X : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hXX : 0 < X * X) (hQ : 0 < Q2) (hV : 0 < V2) (hC : 0 < C2)
    (ht : t = a * s + b * V2)
    (key : t * t * Q2 - s * s * C2 = X * X * (2 * a * b * s + b * b * V2)) :
    s * |s| * C2 < t * |t| * Q2 := by
  rcases le_or_gt 0 s with hs | hs
  · have htpos : 0 < t := by
      rw [ht]
      nlinarith [mul_nonneg ha.le hs, mul_pos hb hV]
    rw [abs_of_nonneg hs, abs_of_pos htpos]
    have h1 : 0 < 2 * a * b * s + b * b * V2 := by
      nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) hs, mul_pos (mul_pos hb hb) hV]
    nlinarith [mul_pos hXX h1]
  · rw [abs_of_neg hs]
    rcases le_or_gt 0 t with htn | htn
    · rw [abs_of_nonneg htn]
      nlinarith [mul_pos (mul_pos (neg_pos.mpr hs) (neg_pos.mpr hs)) hC,
        mul_nonneg (mul_nonneg htn htn) hQ.le]
    · rw [abs_of_neg htn]
      have h1 : 2 * a * b * s + b * b * V2 < 0 := by
        have e : 2 * a * b * s + b * b * V2 = b * (t + a * s) := by
          rw [ht]
          ring
        rw [e]
        exact mul_neg_of_pos_of_neg hb (by nlinarith [mul_pos ha (neg_pos.mpr hs)])
      nlinarith [mul_neg_of_pos_of_neg hXX h1]

/-- A positive combination `c = a u + b v` makes a strictly smaller angle with `v`
    than `u` does, when `u` and `v` are not parallel. -/
theorem vecKey_lt_of_comb (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (u v c : ℤ × ℤ)
    (hc1 : c.1 = a * u.1 + b * v.1) (hc2 : c.2 = a * u.2 + b * v.2)
    (hX : v.1 * u.2 - v.2 * u.1 ≠ 0) : vecKey c v < vecKey u v := by
  obtain ⟨q1, q2⟩ := u
  obtain ⟨v1, v2⟩ := v
  obtain ⟨c1, c2⟩ := c
  simp only at hc1 hc2 hX
  subst hc1 hc2
  have hXX : 0 < (v1 * q2 - v2 * q1) * (v1 * q2 - v2 * q1) := mul_self_pos.mpr hX
  have lagq : (q1 * v1 + q2 * v2) * (q1 * v1 + q2 * v2) +
      (v1 * q2 - v2 * q1) * (v1 * q2 - v2 * q1) = (q1 * q1 + q2 * q2) * (v1 * v1 + v2 * v2) := by
    ring
  have lagc : ((a * q1 + b * v1) * v1 + (a * q2 + b * v2) * v2) *
        ((a * q1 + b * v1) * v1 + (a * q2 + b * v2) * v2) +
      a * a * ((v1 * q2 - v2 * q1) * (v1 * q2 - v2 * q1)) =
      ((a * q1 + b * v1) * (a * q1 + b * v1) + (a * q2 + b * v2) * (a * q2 + b * v2)) *
        (v1 * v1 + v2 * v2) := by
    ring
  have hQ0 : 0 ≤ q1 * q1 + q2 * q2 := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hV0 : 0 ≤ v1 * v1 + v2 * v2 := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hC0 : 0 ≤ (a * q1 + b * v1) * (a * q1 + b * v1) + (a * q2 + b * v2) * (a * q2 + b * v2) :=
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hQV : 0 < (q1 * q1 + q2 * q2) * (v1 * v1 + v2 * v2) := by
    rw [← lagq]
    nlinarith [mul_self_nonneg (q1 * v1 + q2 * v2)]
  have hQ : 0 < q1 * q1 + q2 * q2 := by
    rcases hQ0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hQV
      exact absurd hQV (lt_irrefl 0)
  have hV : 0 < v1 * v1 + v2 * v2 := by
    rcases hV0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hQV
      exact absurd hQV (lt_irrefl 0)
  have hCV : 0 < ((a * q1 + b * v1) * (a * q1 + b * v1) + (a * q2 + b * v2) * (a * q2 + b * v2)) *
      (v1 * v1 + v2 * v2) := by
    rw [← lagc]
    nlinarith [mul_self_nonneg ((a * q1 + b * v1) * v1 + (a * q2 + b * v2) * v2),
      mul_pos (mul_pos ha ha) hXX]
  have hC : 0 < (a * q1 + b * v1) * (a * q1 + b * v1) + (a * q2 + b * v2) * (a * q2 + b * v2) := by
    rcases hC0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hCV
      exact absurd hCV (lt_irrefl 0)
  have h := key_lt_abstract a b (q1 * v1 + q2 * v2)
    ((a * q1 + b * v1) * v1 + (a * q2 + b * v2) * v2)
    ((a * q1 + b * v1) * (a * q1 + b * v1) + (a * q2 + b * v2) * (a * q2 + b * v2))
    (q1 * q1 + q2 * q2) (v1 * v1 + v2 * v2) (v1 * q2 - v2 * q1) ha hb hXX hQ hV hC
    (by ring) (by ring)
  unfold vecKey
  simp only
  have hQq : (0 : ℚ) < ((q1 * q1 + q2 * q2 : ℤ) : ℚ) := by exact_mod_cast hQ
  have hCq : (0 : ℚ) < (((a * q1 + b * v1) * (a * q1 + b * v1) +
      (a * q2 + b * v2) * (a * q2 + b * v2) : ℤ) : ℚ) := by exact_mod_cast hC
  rw [neg_div, neg_div, neg_lt_neg_iff, div_lt_div_iff₀ hQq hCq]
  exact_mod_cast h

/-- All points of one half-line from `K` have the same key: if `K` is `n` steps of
    `d` from `P` and `B` is `j` steps, with `0 ≤ j < n`, then `B` and `P` have the
    same key. -/
theorem angleKey_eq_of_ray (K L P B : Pos) (d : Dir) (j n : ℤ) (hj : 0 ≤ j) (hjn : j < n)
    (hB : B.toInt = (P.toInt.1 + j * d.1, P.toInt.2 + j * d.2))
    (hK : K.toInt = (P.toInt.1 + n * d.1, P.toInt.2 + n * d.2)) :
    angleKey K L B = angleKey K L P := by
  have b1 : B.toInt.1 = P.toInt.1 + j * d.1 := congrArg Prod.fst hB
  have b2 : B.toInt.2 = P.toInt.2 + j * d.2 := congrArg Prod.snd hB
  have k1 : K.toInt.1 = P.toInt.1 + n * d.1 := congrArg Prod.fst hK
  have k2 : K.toInt.2 = P.toInt.2 + n * d.2 := congrArg Prod.snd hK
  unfold angleKey
  -- `n (B - K) = (n - j) (P - K)`: both are `n (j - n) d`.
  rw [← vecKey_of_mul n (by omega) (B.toInt.1 - K.toInt.1, B.toInt.2 - K.toInt.2)
      (n * (B.toInt.1 - K.toInt.1), n * (B.toInt.2 - K.toInt.2)) _ rfl rfl]
  exact vecKey_of_mul (n - j) (by omega) _ _ _
    (by simp only; rw [b1, k1]; ring) (by simp only; rw [b2, k2]; ring)

/-- An interposition lowers the angle (the geometry of Remark 4.4): if `L` is `n`
    steps of `d` from `Q` and `C` is `j` steps, with `0 < j < n`, then `C` has a
    smaller key than `Q`, unless `Q` is on the line through `K` and `L`. -/
theorem angleKey_lt_of_between (K L Q C : Pos) (d : Dir) (j n : ℤ) (hj : 0 < j) (hjn : j < n)
    (hC : C.toInt = (Q.toInt.1 + j * d.1, Q.toInt.2 + j * d.2))
    (hL : L.toInt = (Q.toInt.1 + n * d.1, Q.toInt.2 + n * d.2))
    (hQ : lineSide K L Q ≠ 0) :
    angleKey K L C < angleKey K L Q := by
  have c1 : C.toInt.1 = Q.toInt.1 + j * d.1 := congrArg Prod.fst hC
  have c2 : C.toInt.2 = Q.toInt.2 + j * d.2 := congrArg Prod.snd hC
  have l1 : L.toInt.1 = Q.toInt.1 + n * d.1 := congrArg Prod.fst hL
  have l2 : L.toInt.2 = Q.toInt.2 + n * d.2 := congrArg Prod.snd hL
  unfold angleKey
  -- `n (C - K) = (n - j) (Q - K) + j (L - K)`.
  rw [← vecKey_of_mul n (by omega) (C.toInt.1 - K.toInt.1, C.toInt.2 - K.toInt.2)
      (n * (C.toInt.1 - K.toInt.1), n * (C.toInt.2 - K.toInt.2)) _ rfl rfl]
  refine vecKey_lt_of_comb (n - j) j (by omega) hj _ _ _ ?_ ?_ ?_
  · simp only
    rw [c1, l1]
    ring
  · simp only
    rw [c2, l2]
    ring
  · simpa only [lineSide] using hQ

end MPC
