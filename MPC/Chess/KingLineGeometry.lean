import MPC.Chess.CheckingRayGeometry

/-! Integer geometry on the line through the two kings. All statements are
independent of trace legality and apply to every queen direction. -/

namespace MPC.Chess

/-- Collinearity, with no order or board-occupancy condition. -/
def Pos.collinear (a b c : Pos) : Prop :=
  (b.toInt.1 - a.toInt.1) * (c.toInt.2 - a.toInt.2) =
    (c.toInt.1 - a.toInt.1) * (b.toInt.2 - a.toInt.2)

instance (a b c : Pos) : Decidable (a.collinear b c) := inferInstanceAs (Decidable (_ = _))

theorem Pos.collinear_swap (a b c : Pos) : a.collinear b c ↔ b.collinear a c := by
  unfold Pos.collinear
  constructor <;> intro h <;> nlinarith only [h]

private theorem pos_ext {a b : Pos} (hx : a.toInt.1 = b.toInt.1)
    (hy : a.toInt.2 = b.toInt.2) : a = b := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [Pos.toInt] at hx hy <;> omega

/-- Collinearity with a nonzero step along a queen direction supplies an
integer parameter for the other board square, in either direction. -/
theorem exists_line_parameter_of_collinear (K L A : Pos) (d : RayDirection) (c : ℤ)
    (hc : c ≠ 0)
    (hA : A.toInt = (K.toInt.1 + c * d.vector.1, K.toInt.2 + c * d.vector.2))
    (hcol : K.collinear L A) :
    ∃ t : ℤ, L.toInt = (K.toInt.1 + t * d.vector.1, K.toInt.2 + t * d.vector.2) := by
  have hx : A.toInt.1 - K.toInt.1 = c * d.vector.1 := by rw [hA]; ring
  have hy : A.toInt.2 - K.toInt.2 = c * d.vector.2 := by rw [hA]; ring
  unfold Pos.collinear at hcol
  rw [hx, hy] at hcol
  have hkey : (L.toInt.1 - K.toInt.1) * d.vector.2 = d.vector.1 * (L.toInt.2 - K.toInt.2) := by
    apply mul_left_cancel₀ hc
    nlinarith only [hcol]
  cases d <;> simp only [RayDirection.vector, mul_one, mul_zero, mul_neg_one, add_zero] at hkey ⊢
  all_goals first
    | exact ⟨L.toInt.1 - K.toInt.1, Prod.ext (by omega) (by omega)⟩
    | exact ⟨K.toInt.1 - L.toInt.1, Prod.ext (by omega) (by omega)⟩
    | exact ⟨L.toInt.2 - K.toInt.2, Prod.ext (by omega) (by omega)⟩
    | exact ⟨K.toInt.2 - L.toInt.2, Prod.ext (by omega) (by omega)⟩

/-- Open-segment membership is exactly strict order of the line parameters. -/
theorem between_iff_line_parameters (o a b q : Pos) (d : RayDirection) (s t u : ℤ)
    (ha : a.toInt = (o.toInt.1 + s * d.vector.1, o.toInt.2 + s * d.vector.2))
    (hb : b.toInt = (o.toInt.1 + t * d.vector.1, o.toInt.2 + t * d.vector.2))
    (hq : q.toInt = (o.toInt.1 + u * d.vector.1, o.toInt.2 + u * d.vector.2)) :
    Between a b q ↔ (s < u ∧ u < t) ∨ (t < u ∧ u < s) := by
  have hqs : q = a ↔ u = s := by
    constructor
    · intro h; rw [h, ha] at hq
      cases d <;> simp only [RayDirection.vector, Prod.mk.injEq] at hq <;> omega
    · intro h; apply pos_ext <;> rw [hq, ha, h]
  have hqt : q = b ↔ u = t := by
    constructor
    · intro h; rw [h, hb] at hq
      cases d <;> simp only [RayDirection.vector, Prod.mk.injEq] at hq <;> omega
    · intro h; apply pos_ext <;> rw [hq, hb, h]
  have hcross : (q.toInt.1 - a.toInt.1) * (b.toInt.2 - a.toInt.2) =
      (q.toInt.2 - a.toInt.2) * (b.toInt.1 - a.toInt.1) := by
    rw [ha, hb, hq]; ring
  simp only [Between, ne_eq, hqs, hqt, hcross, true_and]
  rw [ha, hb, hq]
  cases d <;> simp only [RayDirection.vector, mul_one, mul_zero, mul_neg_one, add_zero]
  all_goals constructor <;> intro h <;> omega

theorem collinear_of_line_parameters (o a b q : Pos) (d : RayDirection) (s t u : ℤ)
    (ha : a.toInt = (o.toInt.1 + s * d.vector.1, o.toInt.2 + s * d.vector.2))
    (hb : b.toInt = (o.toInt.1 + t * d.vector.1, o.toInt.2 + t * d.vector.2))
    (hq : q.toInt = (o.toInt.1 + u * d.vector.1, o.toInt.2 + u * d.vector.2)) :
    a.collinear b q := by
  unfold Pos.collinear
  rw [ha, hb, hq]; ring

/-- If a landing square lies inside a line to one king and the other king
lies outside that segment, either the first king or the line's source blocks
the segment from the landing square to the other king. -/
theorem kingLine_blocker_between {K L B A : Pos}
    (hal : B.aligned K) (hA : Between B K A) (hcol : K.collinear L A)
    (hLK : L ≠ K) (hLB : L ≠ B) (hL : ¬ Between B K L) :
    Between A L K ∨ Between A L B := by
  have hBK : B ≠ K := by
    intro h
    subst B
    have hb := hA.2.2.2
    exact hA.1 (pos_ext (by omega) (by omega))
  obtain ⟨d, hr⟩ := exists_onRay_of_aligned hal hBK
  obtain ⟨n, hn, hnx, hny⟩ := (onRay_iff_positive_steps K B d).mp hr
  obtain ⟨j, hj, hjx, hjy⟩ := (onRay_iff_positive_steps K A d).mp (hr.of_between hA)
  have hB : B.toInt = (K.toInt.1 + n * d.vector.1, K.toInt.2 + n * d.vector.2) := Prod.ext hnx hny
  have hAp : A.toInt = (K.toInt.1 + j * d.vector.1, K.toInt.2 + j * d.vector.2) := Prod.ext hjx hjy
  have hK : K.toInt = (K.toInt.1 + 0 * d.vector.1, K.toInt.2 + 0 * d.vector.2) := by simp
  have hjn := (between_iff_line_parameters K B K A d n 0 j hB hK hAp).mp hA
  obtain ⟨t, hLt⟩ := exists_line_parameter_of_collinear K L A d j (by omega) hAp hcol
  have ht0 : t ≠ 0 := by
    intro h; apply hLK; apply pos_ext <;> rw [hLt, h] <;> simp
  have htn : t ≠ n := by
    intro h; apply hLB; apply pos_ext <;> rw [hLt, hB, h]
  have ht := mt (between_iff_line_parameters K B K L d n 0 t hB hK hLt).mpr hL
  rcases (show t < 0 ∨ n < t by omega) with ht | ht
  · exact Or.inl ((between_iff_line_parameters K A L K d j t 0 hAp hLt hK).mpr (by omega))
  · exact Or.inr ((between_iff_line_parameters K A L B d j t n hAp hLt hB).mpr (by omega))

end MPC.Chess
