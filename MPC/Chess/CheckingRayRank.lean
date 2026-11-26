import MPC.Chess.RayAngleRank
import MPC.Chess.CheckingRayHalfPlane
import MPC.Chess.CheckingCrossingWitness

/-! The Definition 6.5 argument for periodic mutual checks. Lemma 6.4(1) gives
each checking ray two board crossings, and the triangle bound on angle ranks
leaves only the first two directions of each king in a half-plane. If one
half-plane contains a checking ray, these four rays are all checking rays and
meet pairwise on board squares. Sides and ranks are measured from the king of
the given color towards the other king. -/

namespace MPC.Chess.MoveTrace

/-- The rays through a crossing lie on the same side, from either king. -/
theorem checkingCrossing_sides_iff_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (p : PlanePoint)
    (hx : tr.CheckingCrossing (kp 0) p) (c : Color) (d e : RayDirection)
    (hd : OnRationalRay (kp 0 c).toPlane d p)
    (he : OnRationalRay (kp 0 c.opponent).toPlane e p) (side : HalfPlaneSide) :
    d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ↔
      e ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side := by
  obtain ⟨s, ⟨_, hs⟩, _⟩ :=
    tr.checkingCrossing_halfPlane_unique_of_periodic_checks kp hl hk hc hp hn p hx
  have hd' := hs c d hd
  have he' := hs c.opponent e he
  cases c
  · exact (mem_halfPlaneDirections_iff_side_eq hd' side).trans
      (mem_halfPlaneDirections_iff_side_eq he' side).symm
  · have hsw (x : RayDirection) := mem_halfPlaneDirections_swap (kp 0 .white).toPlane
      (kp 0 .black).toPlane side.opposite x
    simp only [HalfPlaneSide.opposite_opposite] at hsw
    simp only [Color.opponent] at hd' he' ⊢
    rw [hsw d, hsw e, mem_halfPlaneDirections_iff_side_eq hd',
      mem_halfPlaneDirections_iff_side_eq he']

/-- A board crossing on a checking ray lies on a nonparallel checking ray of
the other king, from the same side. The angle ranks add up to at most four. -/
theorem crossing_checkingRay_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) (A : Pos) (hA : A.toPlane ∈ tr.checkingCrossings (kp 0))
    (hdA : OnRay (kp 0 c) d A) :
    ∃ e, tr.CheckingRay (kp 0 c.opponent) c.opponent e ∧ OnRay (kp 0 c.opponent) e A ∧
      rayDet d e ≠ 0 ∧
      kingRayRank (kp 0 c).toPlane (kp 0 c.opponent).toPlane d +
        kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane e ≤ 4 ∧
      ∀ side, d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ↔
        e ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side := by
  have hx := tr.checkingCrossing_of_mem_checkingCrossings (kp 0) A.toPlane hA
  obtain ⟨e, he, heA⟩ := hx c.opponent
  have hAo := tr.checkingCrossing_ne_king_of_periodic_checks kp hl hk hc hp hn _ hx c.opponent
  have hAc := tr.checkingCrossing_ne_king_of_periodic_checks kp hl hk hc hp hn _ hx c
  have hdA' : OnRationalRay (kp 0 c).toPlane d A.toPlane :=
    (onRationalRay_toPlane_iff _ _ _).mpr (Or.inr hdA)
  have hdet : rayDet d e ≠ 0 := fun hz =>
    tr.checkingRay_disjoint_parallel_of_periodic_checks kp hl hk hc hp hn c d e hr hz
      ⟨A.toPlane, hdA', heA⟩
  refine ⟨e, he, ?_, hdet, kingRayRank_add_le_four hdA' heA hAc hAo hdet,
    tr.checkingCrossing_sides_iff_of_periodic_checks kp hl hk hc hp hn _ hx c d e hdA' heA⟩
  rcases (onRationalRay_toPlane_iff _ _ _).mp heA with h | h
  · exact absurd (congrArg Pos.toPlane h) hAo
  · exact h

/-- Lemma 6.4(1) supplies two crossings met by two different rays of the other
king. They are the data of the paper's argument after Definition 6.5. -/
private theorem two_crossing_rays_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) (side : HalfPlaneSide)
    (hs : d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side) :
    ∃ eA eB A B, eA ≠ eB ∧
      tr.CheckingRay (kp 0 c.opponent) c.opponent eA ∧
      tr.CheckingRay (kp 0 c.opponent) c.opponent eB ∧
      OnRay (kp 0 c) d A ∧ OnRay (kp 0 c.opponent) eA A ∧
      OnRay (kp 0 c) d B ∧ OnRay (kp 0 c.opponent) eB B ∧
      eA ∈ halfPlaneDirections (kp 0 c.opponent).toPlane (kp 0 c).toPlane side.opposite ∧
      eB ∈ halfPlaneDirections (kp 0 c.opponent).toPlane (kp 0 c).toPlane side.opposite ∧
      kingRayRank (kp 0 c).toPlane (kp 0 c.opponent).toPlane d +
        kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane eA ≤ 4 ∧
      kingRayRank (kp 0 c).toPlane (kp 0 c.opponent).toPlane d +
        kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane eB ≤ 4 := by
  obtain ⟨A, B, hAB, hA, hB, hdA, hdB⟩ :=
    tr.checkingRay_two_crossings_of_periodic_checks kp hl hk hc hp hn c d hr
  obtain ⟨eA, heA, hAe, hdetA, hsumA, hsideA⟩ :=
    tr.crossing_checkingRay_of_periodic_checks kp hl hk hc hp hn c d hr A hA hdA
  obtain ⟨eB, heB, hBe, _, hsumB, hsideB⟩ :=
    tr.crossing_checkingRay_of_periodic_checks kp hl hk hc hp hn c d hr B hB hdB
  refine ⟨eA, eB, A, B, ?_, heA, heB, hdA, hAe, hdB, hBe,
    (mem_halfPlaneDirections_swap _ _ _ _).mpr ((hsideA side).mp hs),
    (mem_halfPlaneDirections_swap _ _ _ _).mpr ((hsideB side).mp hs), hsumA, hsumB⟩
  rintro rfl
  apply hAB
  apply Pos.toPlane_injective
  have hon (q : Pos) (h : OnRay (kp 0 c) d q) (h' : OnRay (kp 0 c.opponent) eA q) :
      OnRationalRay (kp 0 c).toPlane d q.toPlane ∧
        OnRationalRay (kp 0 c.opponent).toPlane eA q.toPlane :=
    ⟨(onRationalRay_toPlane_iff _ _ _).mpr (Or.inr h),
      (onRationalRay_toPlane_iff _ _ _).mpr (Or.inr h')⟩
  exact rationalRay_intersection_unique hdetA (hon A hdA hAe) (hon B hdB hBe)

/-- Definition 6.5 in the paper: `l₃`, `l₄`, `k₃` and `k₄` are not checking
rays. Every checking ray makes an angle of at most 90° with the king line. -/
theorem checkingRay_rank_le_two_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) :
    kingRayRank (kp 0 c).toPlane (kp 0 c.opponent).toPlane d ≤ 2 := by
  obtain ⟨side, hs⟩ := exists_mem_halfPlaneDirections
    (tr.checkingRay_offset_ne_zero_of_periodic_checks kp hl hk hc hp hn c d hr)
  obtain ⟨eA, eB, _, _, hne, _, _, _, _, _, _, hsA, hsB, hsumA, hsumB⟩ :=
    two_crossing_rays_of_periodic_checks tr kp hl hk hc hp hn c d hr side hs
  have hrank := kingRayRank_injOn _ _ side.opposite (Finset.mem_coe.mpr hsA)
    (Finset.mem_coe.mpr hsB)
  have h₁ := kingRayRank_pos (kp 0 c.opponent).toPlane (kp 0 c).toPlane eA
  have h₂ := kingRayRank_pos (kp 0 c.opponent).toPlane (kp 0 c).toPlane eB
  by_contra h
  apply hne
  apply hrank
  omega

/-- A checking ray meets both checking rays of rank 1 and 2 of the other king
in its half-plane, each on a board square. -/
theorem checkingRay_meets_rank_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) (side : HalfPlaneSide)
    (hs : d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side)
    (i : ℕ) (hi : i = 1 ∨ i = 2) :
    ∃ e, tr.CheckingRay (kp 0 c.opponent) c.opponent e ∧
      e ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane e = i ∧
      ∃ q : Pos, OnRay (kp 0 c) d q ∧ OnRay (kp 0 c.opponent) e q := by
  obtain ⟨eA, eB, A, B, hne, heA, heB, hdA, hAe, hdB, hBe, hsA, hsB, _, _⟩ :=
    two_crossing_rays_of_periodic_checks tr kp hl hk hc hp hn c d hr side hs
  have hrank := kingRayRank_injOn _ _ side.opposite (Finset.mem_coe.mpr hsA)
    (Finset.mem_coe.mpr hsB)
  have hA2 := tr.checkingRay_rank_le_two_of_periodic_checks kp hl hk hc hp hn c.opponent eA heA
  have hB2 := tr.checkingRay_rank_le_two_of_periodic_checks kp hl hk hc hp hn c.opponent eB heB
  simp only [Color.opponent_opponent] at hA2 hB2
  have h₁ := kingRayRank_pos (kp 0 c.opponent).toPlane (kp 0 c).toPlane eA
  have h₂ := kingRayRank_pos (kp 0 c.opponent).toPlane (kp 0 c).toPlane eB
  have hd : kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane eA ≠
      kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane eB := fun h => hne (hrank h)
  by_cases hiA : kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane eA = i
  · exact ⟨eA, heA, (mem_halfPlaneDirections_swap _ _ _ _).mp hsA, hiA, A, hdA, hAe⟩
  · exact ⟨eB, heB, (mem_halfPlaneDirections_swap _ _ _ _).mp hsB, by omega, B, hdB, hBe⟩

/-- The paper's conclusion after Definition 6.5: if a half-plane contains a
checking ray, then `l₁`, `l₂`, `k₁` and `k₂` are exactly the checking rays in it,
and `l₁`/`k₁`, `l₁`/`k₂`, `l₂`/`k₁`, `l₂`/`k₂` meet on board squares. Here `u`
are the rays of `c` and `v` those of the other king, numbered by rank. -/
theorem halfPlane_checkingRays_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (side : HalfPlaneSide)
    (d₀ : RayDirection) (h₀ : tr.CheckingRay (kp 0 c) c d₀)
    (hs₀ : d₀ ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side) :
    ∃ u₁ u₂ v₁ v₂ : RayDirection,
      kingRayRank (kp 0 c).toPlane (kp 0 c.opponent).toPlane u₁ = 1 ∧
      kingRayRank (kp 0 c).toPlane (kp 0 c.opponent).toPlane u₂ = 2 ∧
      kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane v₁ = 1 ∧
      kingRayRank (kp 0 c.opponent).toPlane (kp 0 c).toPlane v₂ = 2 ∧
      (∀ d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side,
        tr.CheckingRay (kp 0 c) c d ↔ d = u₁ ∨ d = u₂) ∧
      (∀ e ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side,
        tr.CheckingRay (kp 0 c.opponent) c.opponent e ↔ e = v₁ ∨ e = v₂) ∧
      u₁ ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      u₂ ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      v₁ ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      v₂ ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      ∀ d, (d = u₁ ∨ d = u₂) → ∀ e, (e = v₁ ∨ e = v₂) →
        ∃ q : Pos, OnRay (kp 0 c) d q ∧ OnRay (kp 0 c.opponent) e q := by
  set K := (kp 0 c).toPlane
  set L := (kp 0 c.opponent).toPlane
  have meets := tr.checkingRay_meets_rank_of_periodic_checks kp hl hk hc hp hn
  obtain ⟨v₁, hv₁, hsv₁, hrv₁, -⟩ := meets c d₀ h₀ side hs₀ 1 (Or.inl rfl)
  obtain ⟨v₂, hv₂, hsv₂, hrv₂, -⟩ := meets c d₀ h₀ side hs₀ 2 (Or.inr rfl)
  have hsv₁' : v₁ ∈ halfPlaneDirections (kp 0 c.opponent).toPlane
      (kp 0 c.opponent.opponent).toPlane side.opposite := by
    rw [Color.opponent_opponent]; exact (mem_halfPlaneDirections_swap _ _ _ _).mpr hsv₁
  have mu (i : ℕ) (hi : i = 1 ∨ i = 2) :
      ∃ u, tr.CheckingRay (kp 0 c) c u ∧ u ∈ halfPlaneDirections K L side ∧
        kingRayRank K L u = i := by
    obtain ⟨u, hu, hsu, hru, -⟩ := meets c.opponent v₁ hv₁ side.opposite hsv₁' i hi
    simp only [Color.opponent_opponent] at hu hsu hru
    exact ⟨u, hu, (mem_halfPlaneDirections_swap _ _ _ _).mp hsu, hru⟩
  obtain ⟨u₁, hu₁, hsu₁, hru₁⟩ := mu 1 (Or.inl rfl)
  obtain ⟨u₂, hu₂, hsu₂, hru₂⟩ := mu 2 (Or.inr rfl)
  have injK := kingRayRank_injOn K L side
  have injL := kingRayRank_injOn L K side.opposite
  have toL {e : RayDirection} (h : e ∈ halfPlaneDirections K L side) :
      (e : RayDirection) ∈ (halfPlaneDirections L K side.opposite : Set RayDirection) :=
    Finset.mem_coe.mpr ((mem_halfPlaneDirections_swap _ _ _ _).mpr h)
  have le₂ := tr.checkingRay_rank_le_two_of_periodic_checks kp hl hk hc hp hn
  refine ⟨u₁, u₂, v₁, v₂, hru₁, hru₂, hrv₁, hrv₂, ?_, ?_, hsu₁, hsu₂, hsv₁, hsv₂, ?_⟩
  · intro d hd
    constructor
    · intro h
      have h₂ := le₂ c d h
      change kingRayRank K L d ≤ 2 at h₂
      have h₁ := kingRayRank_pos K L d
      by_cases hr : kingRayRank K L d = 1
      · exact Or.inl (injK (Finset.mem_coe.mpr hd) (Finset.mem_coe.mpr hsu₁) (hr.trans hru₁.symm))
      · exact Or.inr (injK (Finset.mem_coe.mpr hd) (Finset.mem_coe.mpr hsu₂)
          ((show kingRayRank K L d = 2 by omega).trans hru₂.symm))
    · rintro (rfl | rfl) <;> assumption
  · intro e he
    constructor
    · intro h
      have h₂ := le₂ c.opponent e h
      simp only [Color.opponent_opponent] at h₂
      change kingRayRank L K e ≤ 2 at h₂
      have h₁ := kingRayRank_pos L K e
      by_cases hr : kingRayRank L K e = 1
      · exact Or.inl (injL (toL he) (toL hsv₁) (hr.trans hrv₁.symm))
      · exact Or.inr (injL (toL he) (toL hsv₂)
          ((show kingRayRank L K e = 2 by omega).trans hrv₂.symm))
    · rintro (rfl | rfl) <;> assumption
  · intro d hd e he
    have hdc : tr.CheckingRay (kp 0 c) c d ∧ d ∈ halfPlaneDirections K L side := by
      rcases hd with rfl | rfl
      exacts [⟨hu₁, hsu₁⟩, ⟨hu₂, hsu₂⟩]
    have hei : ∃ i, (i = 1 ∨ i = 2) ∧ kingRayRank L K e = i ∧
        e ∈ halfPlaneDirections K L side := by
      rcases he with rfl | rfl
      exacts [⟨1, Or.inl rfl, hrv₁, hsv₁⟩, ⟨2, Or.inr rfl, hrv₂, hsv₂⟩]
    obtain ⟨i, hi, hre, hse⟩ := hei
    obtain ⟨e', -, hse', hre', q, hq, hq'⟩ := meets c d hdc.1 side hdc.2 i hi
    have : e' = e := injL (toL hse') (toL hse) (hre'.trans hre.symm)
    exact ⟨q, hq, this ▸ hq'⟩

end MPC.Chess.MoveTrace
