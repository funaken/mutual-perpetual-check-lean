import MPC.Chess.LatticeFrame

/-! One half-plane of Figure 3 in canonical coordinates. Board squares differ by
at most seven in each coordinate, and a lattice frame puts the other king at
`(a, b)` with `0 ≤ b ≤ a`. With the canonical north in the half-plane, the
rank-1 and rank-2 rays are read off exactly. Kings on a common
axis or diagonal leave the two rank-2 rays parallel, so the four crossings
cannot all exist. Otherwise the crossings are `(b, b)`, `((a+b)/2, (a+b)/2)`,
`(0, b)` and `(0, a+b)`; integrality and the board bound leave three shapes. -/

namespace MPC.Chess

open LatticeFrame

/-- A frame displacement between two board squares has integer image coordinates. -/
theorem apply_eq_toInt_sub {p q : Pos} {F : LatticeFrame} {v : PlanePoint}
    (h : q.toPlane = p.toPlane + F.apply v) :
    (F.apply v).1 = ((q.toInt.1 - p.toInt.1 : ℤ) : ℚ) ∧
      (F.apply v).2 = ((q.toInt.2 - p.toInt.2 : ℤ) : ℚ) := by
  constructor
  · have := congrArg Prod.fst h
    simp only [Pos.toPlane, Prod.fst_add] at this
    push_cast; linarith
  · have := congrArg Prod.snd h
    simp only [Pos.toPlane, Prod.snd_add] at this
    push_cast; linarith

/-- Two board squares differ by at most seven in each canonical coordinate. -/
theorem abs_le_seven_of_frame {p q : Pos} {F : LatticeFrame} {v : PlanePoint}
    (h : q.toPlane = p.toPlane + F.apply v) : |v.1| ≤ 7 ∧ |v.2| ≤ 7 := by
  obtain ⟨hx, hy⟩ := apply_eq_toInt_sub h
  have bx : |(F.apply v).1| ≤ 7 := by
    rw [hx]
    have : |q.toInt.1 - p.toInt.1| ≤ 7 := by
      simp only [Pos.toInt]; have := q.1.isLt; have := p.1.isLt; rw [abs_le]; omega
    exact_mod_cast this
  have bY : |(F.apply v).2| ≤ 7 := by
    rw [hy]
    have : |q.toInt.2 - p.toInt.2| ≤ 7 := by
      simp only [Pos.toInt]; have := q.2.isLt; have := p.2.isLt; rw [abs_le]; omega
    exact_mod_cast this
  rcases F.abs_apply v with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ bx, h2 ▸ bY⟩
  · exact ⟨h2 ▸ bY, h1 ▸ bx⟩

/-- A board square on rays from both kings gives an exact equation in canonical
coordinates. -/
theorem frame_crossing_eq {K L q : Pos} {F : LatticeFrame} {w : PlanePoint}
    (hL : L.toPlane = K.toPlane + F.apply w) {dk dl : RayDirection}
    (h₁ : OnRay K (F.dir dk) q) (h₂ : OnRay L (F.dir dl) q) :
    ∃ t s : ℚ, 0 < t ∧ 0 < s ∧ q.toPlane = K.toPlane + F.apply (rayPoint (0, 0) dk t) ∧
      rayPoint (0, 0) dk t = w + rayPoint (0, 0) dl s := by
  obtain ⟨t, ht, e₁⟩ := (onRay_dir_iff K q F dk).mp h₁
  obtain ⟨s, hs, e₂⟩ := (onRay_dir_iff L q F dl).mp h₂
  refine ⟨t, s, ht, hs, e₁, F.apply_injective ?_⟩
  rw [F.apply_add]
  have h := e₁.symm.trans e₂
  rw [hL, add_assoc] at h
  exact add_left_cancel h

private theorem exists_frame_int (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    ∃ (F : LatticeFrame) (a b : ℤ), 0 ≤ b ∧ b ≤ a ∧ 0 < a ∧
      (F.apply ((a : ℚ), (b : ℚ))).1 = x ∧ (F.apply ((a : ℚ), (b : ℚ))).2 = y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rcases le_total y x with hb | hb
    · exact ⟨⟨false, false, false⟩, x, y, hy, hb, by omega, by simp [apply], by simp [apply]⟩
    · exact ⟨⟨true, false, false⟩, y, x, hx, hb, by omega, by simp [apply], by simp [apply]⟩
  · rcases le_total (-y) x with hb | hb
    · exact ⟨⟨false, false, true⟩, x, -y, by omega, hb, by omega, by simp [apply],
        by simp [apply]⟩
    · exact ⟨⟨true, false, true⟩, -y, x, hx, hb, by omega, by simp [apply], by simp [apply]⟩
  · rcases le_total y (-x) with hb | hb
    · exact ⟨⟨false, true, false⟩, -x, y, hy, hb, by omega, by simp [apply], by simp [apply]⟩
    · exact ⟨⟨true, true, false⟩, y, -x, by omega, hb, by omega, by simp [apply],
        by simp [apply]⟩
  · rcases le_total (-y) (-x) with hb | hb
    · exact ⟨⟨false, true, true⟩, -x, -y, by omega, hb, by omega, by simp [apply],
        by simp [apply]⟩
    · exact ⟨⟨true, true, true⟩, -y, -x, by omega, hb, by omega, by simp [apply],
        by simp [apply]⟩

/-- Canonical coordinates of the other king: an octant with `0 ≤ b ≤ a`. -/
theorem exists_frame_canonical (K L : Pos) (hne : K ≠ L) :
    ∃ (F : LatticeFrame) (a b : ℤ), 0 ≤ b ∧ b ≤ a ∧ 0 < a ∧
      L.toPlane = K.toPlane + F.apply ((a : ℚ), (b : ℚ)) := by
  have hxy : L.toInt.1 - K.toInt.1 ≠ 0 ∨ L.toInt.2 - K.toInt.2 ≠ 0 := by
    by_contra! h
    apply hne
    apply Prod.ext <;> apply Fin.ext <;> simp only [Pos.toInt] at h <;> omega
  obtain ⟨F, a, b, hb, hba, ha, h1, h2⟩ := exists_frame_int _ _ hxy
  refine ⟨F, a, b, hb, hba, ha, ?_⟩
  ext
  · simp only [Pos.toPlane, Prod.fst_add, h1]; push_cast; ring
  · simp only [Pos.toPlane, Prod.snd_add, h2]; push_cast; ring

/-- Closes `k = angleRank c e` for concrete canonical directions by linear arithmetic. -/
local macro "rank_tac" : tactic => `(tactic|
  (simp only [angleRank, RayDirection.vector, Int.cast_zero, Int.cast_one, Int.cast_neg]
   split_ifs <;> first | rfl | (exfalso; linarith)))

theorem side_sign_mul_det_of_north {K L : PlanePoint} {F : LatticeFrame} {a b : ℚ}
    (hL : L = K + F.apply (a, b)) (ha : 0 < a) {side : HalfPlaneSide}
    (hN : F.dir .north ∈ halfPlaneDirections K L side) : side.sign * F.det = 1 := by
  rw [mem_halfPlaneDirections_dir hL] at hN
  simp only [RayDirection.vector, Int.cast_one, Int.cast_zero, mul_one, mul_zero,
    sub_zero] at hN
  rcases F.det_cases with h | h <;> cases side <;>
    simp only [HalfPlaneSide.sign, h, one_mul, mul_one, neg_mul, mul_neg, neg_neg] at hN ⊢ <;>
    (exfalso; linarith)

/-- Figure 3, one half-plane: given the four rank-1/rank-2 rays of Definition 6.5
and their four board crossings, the kings and rays are one of the three upper
candidates of Figure 3, up to the frame. The crossing `(0, a+b)` is on the board. -/
theorem halfPlane_figure3 {K L : Pos} {F : LatticeFrame} {a b : ℤ} {side : HalfPlaneSide}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : 0 < a)
    (hL : L.toPlane = K.toPlane + F.apply ((a : ℚ), (b : ℚ)))
    (hN : F.dir .north ∈ halfPlaneDirections K.toPlane L.toPlane side)
    {u₁ u₂ v₁ v₂ : RayDirection}
    (hu₁ : kingRayRank K.toPlane L.toPlane u₁ = 1) (hu₂ : kingRayRank K.toPlane L.toPlane u₂ = 2)
    (hv₁ : kingRayRank L.toPlane K.toPlane v₁ = 1) (hv₂ : kingRayRank L.toPlane K.toPlane v₂ = 2)
    (hsu₁ : u₁ ∈ halfPlaneDirections K.toPlane L.toPlane side)
    (hsu₂ : u₂ ∈ halfPlaneDirections K.toPlane L.toPlane side)
    (hsv₁ : v₁ ∈ halfPlaneDirections K.toPlane L.toPlane side)
    (hsv₂ : v₂ ∈ halfPlaneDirections K.toPlane L.toPlane side)
    (hx : ∀ d, (d = u₁ ∨ d = u₂) → ∀ e, (e = v₁ ∨ e = v₂) →
      ∃ q : Pos, OnRay K d q ∧ OnRay L e q) :
    ((a = 3 ∧ b = 1) ∨ (a = 5 ∧ b = 1) ∨ (a = 4 ∧ b = 2)) ∧
      u₁ = F.dir .northEast ∧ u₂ = F.dir .north ∧ v₁ = F.dir .west ∧
      v₂ = F.dir .northWest ∧ ∃ q : Pos, q.toPlane = K.toPlane + F.apply (0, ((a + b : ℤ) : ℚ)) := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) ≤ b := by exact_mod_cast hb
  have hbaQ : (b : ℚ) ≤ a := by exact_mod_cast hba
  have hσ := side_sign_mul_det_of_north hL haQ hN
  have hmem (m : RayDirection) : F.dir m ∈ halfPlaneDirections K.toPlane L.toPlane side ↔
      0 < (a : ℚ) * m.vector.2 - (b : ℚ) * m.vector.1 := by
    rw [mem_halfPlaneDirections_dir hL, hσ, one_mul]
  have injK := kingRayRank_injOn K.toPlane L.toPlane side
  have injL := kingRayRank_injOn L.toPlane K.toPlane side.opposite
  have toL {e : RayDirection} (h : e ∈ halfPlaneDirections K.toPlane L.toPlane side) :
      e ∈ (halfPlaneDirections L.toPlane K.toPlane side.opposite : Set RayDirection) :=
    Finset.mem_coe.mpr ((mem_halfPlaneDirections_swap _ _ _ _).mpr h)
  have toK {e : RayDirection} (h : e ∈ halfPlaneDirections K.toPlane L.toPlane side) :
      e ∈ (halfPlaneDirections K.toPlane L.toPlane side : Set RayDirection) :=
    Finset.mem_coe.mpr h
  have rK (m : RayDirection) (h : F.dir m ∈ halfPlaneDirections K.toPlane L.toPlane side) :
      kingRayRank K.toPlane L.toPlane (F.dir m) =
        angleRank ((a : ℚ) * m.vector.2 - b * m.vector.1) (a * m.vector.1 + b * m.vector.2) := by
    rw [kingRayRank_of_mem h, rayOffset_dir hL, rayDot_dir hL, ← mul_assoc, hσ, one_mul]
  have rL (m : RayDirection) (h : F.dir m ∈ halfPlaneDirections K.toPlane L.toPlane side) :
      kingRayRank L.toPlane K.toPlane (F.dir m) =
        angleRank ((a : ℚ) * m.vector.2 - b * m.vector.1) (-(a * m.vector.1 + b * m.vector.2)) := by
    rw [kingRayRank_of_mem ((mem_halfPlaneDirections_swap _ _ _ _).mpr h), rayOffset_swap,
      rayDot_swap, rayOffset_dir hL, rayDot_dir hL]
    congr 1
    have : side.opposite.sign = -side.sign := by cases side <;> simp [HalfPlaneSide.opposite,
      HalfPlaneSide.sign]
    rw [this, neg_mul_neg, ← mul_assoc, hσ, one_mul]
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · -- Kings on an axis: both rank-2 rays are the canonical north.
    exfalso
    subst hb0
    have hu : u₂ = F.dir .north := injK (toK hsu₂) (toK hN) (by
      rw [hu₂, rK _ hN]; rank_tac)
    have hv : v₂ = F.dir .north := injL (toL hsv₂) (toL hN) (by
      rw [hv₂, rL _ hN]; rank_tac)
    obtain ⟨q, h₁, h₂⟩ := hx u₂ (Or.inr rfl) v₂ (Or.inr rfl)
    rw [hu] at h₁; rw [hv] at h₂
    obtain ⟨t, s, -, -, -, he⟩ := frame_crossing_eq hL h₁ h₂
    simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he
    norm_num at he
    linarith [he.1]
  rcases eq_or_lt_of_le hba with hab | hablt
  · -- Kings on a diagonal: both rank-2 rays are the canonical northwest.
    exfalso
    subst hab
    have hNW : F.dir .northWest ∈ halfPlaneDirections K.toPlane L.toPlane side := by
      rw [hmem]; norm_num [RayDirection.vector]; linarith
    have hu : u₂ = F.dir .northWest := injK (toK hsu₂) (toK hNW) (by
      rw [hu₂, rK _ hNW]; rank_tac)
    have hv : v₂ = F.dir .northWest := injL (toL hsv₂) (toL hNW) (by
      rw [hv₂, rL _ hNW]; rank_tac)
    obtain ⟨q, h₁, h₂⟩ := hx u₂ (Or.inr rfl) v₂ (Or.inr rfl)
    rw [hu] at h₁; rw [hv] at h₂
    obtain ⟨t, s, -, -, -, he⟩ := frame_crossing_eq hL h₁ h₂
    simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he
    norm_num at he
    linarith [he.1, he.2]
  -- Generic kings: identify the four rays and read off the crossings.
  have hbposQ : (0 : ℚ) < b := by exact_mod_cast hbpos
  have hltQ : (b : ℚ) < a := by exact_mod_cast hablt
  have hNE : F.dir .northEast ∈ halfPlaneDirections K.toPlane L.toPlane side := by
    rw [hmem]; norm_num [RayDirection.vector]; linarith
  have hW : F.dir .west ∈ halfPlaneDirections K.toPlane L.toPlane side := by
    rw [hmem]; norm_num [RayDirection.vector]; linarith
  have hNW : F.dir .northWest ∈ halfPlaneDirections K.toPlane L.toPlane side := by
    rw [hmem]; norm_num [RayDirection.vector]; linarith
  have e₁ : u₁ = F.dir .northEast := injK (toK hsu₁) (toK hNE) (by
    rw [hu₁, rK _ hNE]; rank_tac)
  have e₂ : u₂ = F.dir .north := injK (toK hsu₂) (toK hN) (by
    rw [hu₂, rK _ hN]; rank_tac)
  have e₃ : v₁ = F.dir .west := injL (toL hsv₁) (toL hW) (by
    rw [hv₁, rL _ hW]; rank_tac)
  have e₄ : v₂ = F.dir .northWest := injL (toL hsv₂) (toL hNW) (by
    rw [hv₂, rL _ hNW]; rank_tac)
  refine ⟨?_, e₁, e₂, e₃, e₄, ?_⟩
  · -- `(a+b)/2` is a board coordinate and `(0, a+b)` is on the board.
    obtain ⟨q₁, h₁, h₂⟩ := hx u₁ (Or.inl rfl) v₂ (Or.inr rfl)
    rw [e₁] at h₁; rw [e₄] at h₂
    obtain ⟨t, s, -, -, hq, he⟩ := frame_crossing_eq hL h₁ h₂
    simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he
    norm_num at he
    have h2t : 2 * t = a + b := by linarith [he.1, he.2]
    have hint := (apply_eq_toInt_sub hq).1
    simp only [rayPoint, RayDirection.vector] at hint
    norm_num at hint
    obtain ⟨q₂, h₃, h₄⟩ := hx u₂ (Or.inr rfl) v₂ (Or.inr rfl)
    rw [e₂] at h₃; rw [e₄] at h₄
    obtain ⟨t', s', -, -, hq', he'⟩ := frame_crossing_eq hL h₃ h₄
    simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he'
    norm_num at he'
    have hbound := (abs_le_seven_of_frame hq').2
    simp only [rayPoint, RayDirection.vector] at hbound
    norm_num at hbound
    have ht' : t' = a + b := by linarith [he'.1, he'.2]
    rw [ht', abs_le] at hbound
    have hle : a + b ≤ 7 := by exact_mod_cast hbound.2
    rcases (F.apply_fst_cases (t, t)) with h | h | h | h <;> rw [h] at hint <;>
      first
      | (have : a + b = 2 * (q₁.toInt.1 - K.toInt.1) := by
          have : ((a + b : ℤ) : ℚ) = ((2 * (q₁.toInt.1 - K.toInt.1) : ℤ) : ℚ) := by
            push_cast; linarith
          exact_mod_cast this
         omega)
      | (have : a + b = -(2 * (q₁.toInt.1 - K.toInt.1)) := by
          have : ((a + b : ℤ) : ℚ) = ((-(2 * (q₁.toInt.1 - K.toInt.1)) : ℤ) : ℚ) := by
            push_cast; linarith
          exact_mod_cast this
         omega)
  · obtain ⟨q₂, h₃, h₄⟩ := hx u₂ (Or.inr rfl) v₂ (Or.inr rfl)
    rw [e₂] at h₃; rw [e₄] at h₄
    obtain ⟨t', s', -, -, hq', he'⟩ := frame_crossing_eq hL h₃ h₄
    simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he'
    norm_num at he'
    refine ⟨q₂, ?_⟩
    rw [hq']
    have hr : rayPoint (0, 0) RayDirection.north t' = (0, ((a + b : ℤ) : ℚ)) := by
      simp only [rayPoint, RayDirection.vector]
      ext
      · norm_num
      · norm_num; linarith [he'.1, he'.2]
    rw [hr]

end MPC.Chess
