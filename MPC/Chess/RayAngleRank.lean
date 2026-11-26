import MPC.Chess.KingHalfPlane
import Mathlib.Algebra.Order.Ring.Abs

/-! Definition 6.5 without real angles. The angle that a queen direction makes
at a king, measured from the direction towards the other king, is placed in one
of four 45-degree bins by exact comparisons of a dot and a cross product. -/

namespace MPC.Chess

/-- Dot product of the displacement from `a` to `b` with a queen direction. -/
def rayDot (a b : PlanePoint) (d : RayDirection) : ℚ :=
  (b.1 - a.1) * d.vector.1 + (b.2 - a.2) * d.vector.2

/-- For `0 < c`, the angle in `(0°, 180°)` whose cotangent is `e / c` lies in
`(0°, 45°]`, `(45°, 90°]`, `(90°, 135°]` or `(135°, 180°)`, numbered 1 to 4. -/
def angleRank (c e : ℚ) : ℕ :=
  if c ≤ e then 1 else if 0 ≤ e then 2 else if -c ≤ e then 3 else 4

/-- Definition 6.5: the bin of the angle that `d` makes at `o`, measured from the
direction towards `r`. Only directions off the line through `o` and `r` are
ranked by the theorems below; the boundary is excluded by half-plane hypotheses. -/
def kingRayRank (o r : PlanePoint) (d : RayDirection) : ℕ :=
  angleRank |rayOffset o r d| (rayDot o r d)

theorem kingRayRank_pos (o r : PlanePoint) (d : RayDirection) : 1 ≤ kingRayRank o r d := by
  unfold kingRayRank angleRank; split_ifs <;> norm_num

theorem kingRayRank_le_four (o r : PlanePoint) (d : RayDirection) : kingRayRank o r d ≤ 4 := by
  unfold kingRayRank angleRank; split_ifs <;> norm_num

theorem mem_halfPlaneDirections_iff (K L : PlanePoint) (side : HalfPlaneSide)
    (d : RayDirection) : d ∈ halfPlaneDirections K L side ↔ 0 < side.sign * rayOffset K L d := by
  simp [halfPlaneDirections]

@[simp] theorem HalfPlaneSide.opposite_opposite (side : HalfPlaneSide) :
    side.opposite.opposite = side := by
  cases side <;> rfl

theorem rayOffset_swap (K L : PlanePoint) (d : RayDirection) :
    rayOffset L K d = -rayOffset K L d := by
  unfold rayOffset; ring

/-- From the other king, the same global side has the opposite orientation. -/
theorem mem_halfPlaneDirections_swap (K L : PlanePoint) (side : HalfPlaneSide)
    (d : RayDirection) :
    d ∈ halfPlaneDirections L K side.opposite ↔ d ∈ halfPlaneDirections K L side := by
  rw [mem_halfPlaneDirections_iff, mem_halfPlaneDirections_iff, rayOffset_swap]
  cases side <;> simp only [HalfPlaneSide.opposite, HalfPlaneSide.sign] <;>
    constructor <;> intro h <;> linarith

theorem halfPlaneDirections_side_unique {K L : PlanePoint} {side side' : HalfPlaneSide}
    {d : RayDirection} (h : d ∈ halfPlaneDirections K L side)
    (h' : d ∈ halfPlaneDirections K L side') : side = side' := by
  rw [mem_halfPlaneDirections_iff] at h h'
  cases side <;> cases side' <;> simp only [HalfPlaneSide.sign] at h h' <;> first | rfl | linarith

theorem mem_halfPlaneDirections_iff_side_eq {K L : PlanePoint} {s : HalfPlaneSide}
    {d : RayDirection} (h : d ∈ halfPlaneDirections K L s) (side : HalfPlaneSide) :
    d ∈ halfPlaneDirections K L side ↔ side = s :=
  ⟨fun h' => halfPlaneDirections_side_unique h' h, fun e => e ▸ h⟩

theorem exists_mem_halfPlaneDirections {K L : PlanePoint} {d : RayDirection}
    (h : rayOffset K L d ≠ 0) : ∃ side, d ∈ halfPlaneDirections K L side := by
  rcases lt_or_gt_of_ne h with hn | hp
  · exact ⟨.negative, by rw [mem_halfPlaneDirections_iff]; simp [HalfPlaneSide.sign]; linarith⟩
  · exact ⟨.positive, by rw [mem_halfPlaneDirections_iff]; simpa [HalfPlaneSide.sign] using hp⟩

theorem kingRayRank_of_mem {o r : PlanePoint} {side : HalfPlaneSide} {d : RayDirection}
    (h : d ∈ halfPlaneDirections o r side) :
    kingRayRank o r d = angleRank (side.sign * rayOffset o r d) (rayDot o r d) := by
  rw [mem_halfPlaneDirections_iff] at h
  unfold kingRayRank
  congr 1
  cases side <;> simp only [HalfPlaneSide.sign, one_mul, neg_one_mul] at h ⊢
  · exact abs_of_pos h
  · exact abs_of_neg (by linarith)

set_option maxHeartbeats 4000000 in
private theorem angleRank_ne_of_same_side (x y : ℚ) (side : HalfPlaneSide) (d e : RayDirection)
    (hne : d ≠ e) (hd : 0 < side.sign * (x * d.vector.2 - y * d.vector.1))
    (he : 0 < side.sign * (x * e.vector.2 - y * e.vector.1)) :
    angleRank (side.sign * (x * d.vector.2 - y * d.vector.1)) (x * d.vector.1 + y * d.vector.2) ≠
      angleRank (side.sign * (x * e.vector.2 - y * e.vector.1))
        (x * e.vector.1 + y * e.vector.2) := by
  cases side <;> cases d <;> cases e <;> try exact absurd rfl hne
  all_goals
    simp only [HalfPlaneSide.sign, RayDirection.vector, Int.cast_zero, Int.cast_one, Int.cast_neg,
      mul_zero, mul_one, mul_neg, one_mul, neg_mul, sub_zero, zero_sub, add_zero, zero_add,
      neg_neg, sub_neg_eq_add] at hd he ⊢
    unfold angleRank
    split_ifs <;> first | decide | (exfalso; linarith)

/-- Distinct queen directions in one open side have distinct angle ranks. -/
theorem kingRayRank_injOn (o r : PlanePoint) (side : HalfPlaneSide) :
    Set.InjOn (kingRayRank o r) (halfPlaneDirections o r side : Set RayDirection) := by
  intro d hd e he h
  rw [Finset.mem_coe] at hd he
  rw [kingRayRank_of_mem hd, kingRayRank_of_mem he] at h
  rw [mem_halfPlaneDirections_iff] at hd he
  by_contra hne
  exact angleRank_ne_of_same_side (r.1 - o.1) (r.2 - o.2) side d e hne hd he h

private theorem angleRank_add_le_four_of {A E₁ B E₂ : ℚ} (h₁ : -A ≤ E₁) (h₂ : -B ≤ E₂)
    (h₃ : E₁ < 0 → B ≤ E₂) (h₄ : E₁ < A → 0 ≤ E₂) : angleRank A E₁ + angleRank B E₂ ≤ 4 := by
  unfold angleRank
  split_ifs <;> norm_num <;> first
    | linarith [h₃ (by linarith)]
    | linarith [h₄ (by linarith)]

/-- Nonparallel queen directions meet at 45°, 90° or 135°: the cosine never
exceeds the sine, and they agree exactly at 45°. -/
private theorem direction_pair_facts (d e : RayDirection) (h : rayDet d e ≠ 0) :
    (d.vector.1 * e.vector.1 + d.vector.2 * e.vector.2 : ℚ) ≤ |rayDet d e| ∧
      (0 < (d.vector.1 * e.vector.1 + d.vector.2 * e.vector.2 : ℚ) →
        (d.vector.1 * e.vector.1 + d.vector.2 * e.vector.2 : ℚ) = |rayDet d e| ∧
        ((d.vector.1 : ℚ) ^ 2 + d.vector.2 ^ 2) * (e.vector.1 ^ 2 + e.vector.2 ^ 2) =
          2 * (d.vector.1 * e.vector.1 + d.vector.2 * e.vector.2) ^ 2) := by
  revert h
  cases d <;> cases e <;> norm_num [rayDet, RayDirection.vector, abs_one, abs_neg, abs_two]

private theorem direction_norm_pos (d : RayDirection) :
    (0 : ℚ) < (d.vector.1 : ℚ) ^ 2 + d.vector.2 ^ 2 := by
  cases d <;> norm_num [RayDirection.vector]

/-- The paper's triangle argument for Definition 6.5. If a ray from `o` and a
nonparallel ray from `r` meet away from both origins, their angles at `o` and
`r` add up to at most 135°, so their ranks add up to at most 4. In particular a
rank-4 ray meets no ray, and a rank-3 ray meets only rank-1 rays. -/
theorem kingRayRank_add_le_four {o r p : PlanePoint} {d e : RayDirection}
    (hd : OnRationalRay o d p) (he : OnRationalRay r e p) (ho : p ≠ o) (hr : p ≠ r)
    (hde : rayDet d e ≠ 0) : kingRayRank o r d + kingRayRank r o e ≤ 4 := by
  obtain ⟨hd0, hdp⟩ := hd
  obtain ⟨he0, hep⟩ := he
  set t := rayParameter o d p
  set s := rayParameter r e p
  have ht : 0 < t := lt_of_le_of_ne hd0 fun h => ho (by rw [hdp, ← h, rayPoint_zero])
  have hs : 0 < s := lt_of_le_of_ne he0 fun h => hr (by rw [hep, ← h, rayPoint_zero])
  have hx : r.1 - o.1 = t * d.vector.1 - s * e.vector.1 := by
    have h₁ := congrArg Prod.fst hdp
    have h₂ := congrArg Prod.fst hep
    simp only [rayPoint] at h₁ h₂
    linarith
  have hy : r.2 - o.2 = t * d.vector.2 - s * e.vector.2 := by
    have h₁ := congrArg Prod.snd hdp
    have h₂ := congrArg Prod.snd hep
    simp only [rayPoint] at h₁ h₂
    linarith
  have hoff₁ : rayOffset o r d = s * rayDet d e := by
    unfold rayOffset rayDet; rw [hx, hy]; ring
  have hdot₁ : rayDot o r d = t * ((d.vector.1 : ℚ) ^ 2 + d.vector.2 ^ 2) -
      s * (d.vector.1 * e.vector.1 + d.vector.2 * e.vector.2) := by
    unfold rayDot; rw [hx, hy]; ring
  have hoff₂ : rayOffset r o e = -(t * rayDet d e) := by
    unfold rayOffset rayDet
    rw [show o.1 - r.1 = -(r.1 - o.1) by ring, show o.2 - r.2 = -(r.2 - o.2) by ring, hx, hy]
    ring
  have hdot₂ : rayDot r o e = s * ((e.vector.1 : ℚ) ^ 2 + e.vector.2 ^ 2) -
      t * (d.vector.1 * e.vector.1 + d.vector.2 * e.vector.2) := by
    unfold rayDot
    rw [show o.1 - r.1 = -(r.1 - o.1) by ring, show o.2 - r.2 = -(r.2 - o.2) by ring, hx, hy]
    ring
  unfold kingRayRank
  rw [hoff₁, hdot₁, hoff₂, hdot₂, abs_neg, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos ht]
  obtain ⟨hq, h45⟩ := direction_pair_facts d e hde
  have hk : 0 < |rayDet d e| := abs_pos.mpr hde
  have hnd := direction_norm_pos d
  have hne := direction_norm_pos e
  set k := |rayDet d e|
  set q : ℚ := d.vector.1 * e.vector.1 + d.vector.2 * e.vector.2
  set nd : ℚ := (d.vector.1 : ℚ) ^ 2 + d.vector.2 ^ 2
  set ne : ℚ := (e.vector.1 : ℚ) ^ 2 + e.vector.2 ^ 2
  have hsq := mul_le_mul_of_nonneg_left hq hs.le
  have htq := mul_le_mul_of_nonneg_left hq ht.le
  apply angleRank_add_le_four_of
  · linarith [mul_pos ht hnd]
  · linarith [mul_pos hs hne]
  · intro h₁
    rcases le_or_gt q 0 with hq0 | hq0
    · exfalso; linarith [mul_pos ht hnd, mul_nonpos_of_nonneg_of_nonpos hs.le hq0]
    · obtain ⟨hqk, hprod⟩ := h45 hq0
      by_contra h₂
      have hlt := mul_lt_mul'' (show t * nd < s * q by linarith)
        (show s * ne < 2 * t * q by rw [← hqk] at h₂; linarith)
        (mul_pos ht hnd).le (mul_pos hs hne).le
      have heq : t * nd * (s * ne) = s * q * (2 * t * q) := by
        calc t * nd * (s * ne) = t * s * (nd * ne) := by ring
          _ = s * q * (2 * t * q) := by rw [hprod]; ring
      linarith
  · intro h₁
    rcases le_or_gt q 0 with hq0 | hq0
    · linarith [mul_pos hs hne, mul_nonpos_of_nonneg_of_nonpos ht.le hq0]
    · obtain ⟨hqk, hprod⟩ := h45 hq0
      by_contra h₂
      have hlt := mul_lt_mul'' (show s * ne < t * q by linarith)
        (show t * nd < 2 * s * q by rw [← hqk] at h₁; linarith)
        (mul_pos hs hne).le (mul_pos ht hnd).le
      have heq : s * ne * (t * nd) = t * q * (2 * s * q) := by
        calc s * ne * (t * nd) = t * s * (nd * ne) := by ring
          _ = t * q * (2 * s * q) := by rw [hprod]; ring
      linarith

end MPC.Chess
