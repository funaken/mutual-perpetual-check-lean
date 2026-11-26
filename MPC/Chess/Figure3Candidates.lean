import MPC.Chess.Figure3Geometry
import MPC.Chess.CheckingRayRank

/-! Figure 3 for positive-length periodic mutual checks. Some half-plane
contains a checking ray; a lattice frame from one king puts the other king at
`(a, b)` and the canonical north into that half-plane. Part 7c2 then fixes the
four checking rays there and `(a, b) ∈ {(3,1), (5,1), (4,2)}`. If the opposite
half-plane also contains a checking ray, the same analysis seen from the other
king applies, and the two extreme crossings `K + F(0, a+b)` and `K + F(a, -a)`
on the board force `2a + b ≤ 7`, hence `(a, b) = (3, 1)`. The result lists all
checking rays of both kings: the three upper candidates and the lower one. -/

namespace MPC.Chess.MoveTrace

open LatticeFrame

/-- Every move checks, so some king has a checking ray. -/
theorem exists_checkingRay_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) :
    ∃ c d, tr.CheckingRay (kp 0 c) c d := by
  obtain ⟨q, p, hq, ho, hs, ha⟩ := tr.exists_slider_checker_of_periodic_checks kp hl hk hc hp hn 0
  obtain ⟨d, hd, -⟩ := tr.exists_checkingRay_of_slider 0 (kp 0 (tr.states 0).turn) q
    (tr.states 0).turn p hq ho hs ha
  exact ⟨_, d, hd⟩

/-- One half-plane with a checking ray, in a canonical frame of the king of `c`. -/
theorem halfPlane_candidate_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (side : HalfPlaneSide)
    (F : LatticeFrame) (a b : ℤ) (hb : 0 ≤ b) (hba : b ≤ a) (ha : 0 < a)
    (hL : (kp 0 c.opponent).toPlane = (kp 0 c).toPlane + F.apply ((a : ℚ), (b : ℚ)))
    (hN : F.dir .north ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side)
    (d₀ : RayDirection) (h₀ : tr.CheckingRay (kp 0 c) c d₀)
    (hs₀ : d₀ ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side) :
    ((a = 3 ∧ b = 1) ∨ (a = 5 ∧ b = 1) ∨ (a = 4 ∧ b = 2)) ∧
      (∀ d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side,
        tr.CheckingRay (kp 0 c) c d ↔ d = F.dir .northEast ∨ d = F.dir .north) ∧
      (∀ e ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side,
        tr.CheckingRay (kp 0 c.opponent) c.opponent e ↔
          e = F.dir .west ∨ e = F.dir .northWest) ∧
      F.dir .northEast ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      F.dir .north ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      F.dir .west ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      F.dir .northWest ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      ∃ q : Pos, q.toPlane = (kp 0 c).toPlane + F.apply (0, ((a + b : ℤ) : ℚ)) := by
  obtain ⟨u₁, u₂, v₁, v₂, hu₁, hu₂, hv₁, hv₂, hu, hv, hsu₁, hsu₂, hsv₁, hsv₂, hx⟩ :=
    tr.halfPlane_checkingRays_of_periodic_checks kp hl hk hc hp hn c side d₀ h₀ hs₀
  obtain ⟨hab, e₁, e₂, e₃, e₄, hq⟩ :=
    halfPlane_figure3 hb hba ha hL hN hu₁ hu₂ hv₁ hv₂ hsu₁ hsu₂ hsv₁ hsv₂ hx
  subst e₁ e₂ e₃ e₄
  exact ⟨hab, hu, hv, hsu₁, hsu₂, hsv₁, hsv₂, hq⟩

private theorem side_eq_or_opposite (s side : HalfPlaneSide) : s = side ∨ s = side.opposite := by
  cases s <;> cases side <;> simp [HalfPlaneSide.opposite]

/-- Figure 3: up to the frame `F` from the king of `c`, the other king is at
`(a, b) ∈ {(3,1), (5,1), (4,2)}`, the checking rays of `c` are the canonical
northeast and north, and those of the other king are the west and northwest.
When `both` holds, both half-planes contain checking rays (the lower candidate
of Figure 3); then `(a, b) = (3, 1)` and the canonical east and southeast of
`c`, south and southwest of the other king, are checking rays as well. -/
theorem figure3_candidates_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) :
    ∃ (c : Color) (F : LatticeFrame) (a b : ℤ) (both : Prop),
      ((a = 3 ∧ b = 1) ∨ (a = 5 ∧ b = 1) ∨ (a = 4 ∧ b = 2)) ∧ (both → a = 3 ∧ b = 1) ∧
      (kp 0 c.opponent).toPlane = (kp 0 c).toPlane + F.apply ((a : ℚ), (b : ℚ)) ∧
      (∀ d, tr.CheckingRay (kp 0 c) c d ↔ d = F.dir .northEast ∨ d = F.dir .north ∨
        (both ∧ (d = F.dir .east ∨ d = F.dir .southEast))) ∧
      (∀ e, tr.CheckingRay (kp 0 c.opponent) c.opponent e ↔
        e = F.dir .west ∨ e = F.dir .northWest ∨
          (both ∧ (e = F.dir .south ∨ e = F.dir .southWest))) := by
  have cand := tr.halfPlane_candidate_of_periodic_checks kp hl hk hc hp hn
  have rank := tr.halfPlane_checkingRays_of_periodic_checks kp hl hk hc hp hn
  have offset := tr.checkingRay_offset_ne_zero_of_periodic_checks kp hl hk hc hp hn
  have hne (c : Color) : kp 0 c ≠ kp 0 c.opponent := fun h =>
    Color.opponent_ne c ((hk 0).positions_injective h).symm
  -- A half-plane with a checking ray of `c`, oriented by a frame of `c`'s king.
  obtain ⟨c₀, d₀, h₀⟩ := tr.exists_checkingRay_of_periodic_checks kp hl hk hc hp hn
  obtain ⟨s₀, hs₀⟩ := exists_mem_halfPlaneDirections (offset c₀ d₀ h₀)
  obtain ⟨F₀, a, b, hb, hba, ha, hL₀⟩ := exists_frame_canonical _ _ (hne c₀)
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have start : ∃ (c : Color) (F : LatticeFrame) (side : HalfPlaneSide) (d : RayDirection),
      (kp 0 c.opponent).toPlane = (kp 0 c).toPlane + F.apply ((a : ℚ), (b : ℚ)) ∧
      F.dir .north ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
      tr.CheckingRay (kp 0 c) c d ∧
      d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side := by
    have hoff : rayOffset (kp 0 c₀).toPlane (kp 0 c₀.opponent).toPlane (F₀.dir .north) ≠ 0 := by
      rw [rayOffset_dir hL₀]
      simp only [RayDirection.vector, Int.cast_one, Int.cast_zero, mul_one, mul_zero, sub_zero]
      rcases F₀.det_cases with h | h <;> rw [h] <;> linarith
    obtain ⟨s, hs⟩ := exists_mem_halfPlaneDirections hoff
    rcases side_eq_or_opposite s s₀ with rfl | rfl
    · exact ⟨c₀, F₀, s, d₀, hL₀, hs, h₀, hs₀⟩
    · obtain ⟨_, _, v₁, _, _, _, _, _, _, hv, _, _, hsv₁, _, _⟩ := rank c₀ s₀ d₀ h₀ hs₀
      refine ⟨c₀.opponent, F₀.neg, s₀.opposite, v₁, ?_, ?_, (hv v₁ hsv₁).mpr (Or.inl rfl), ?_⟩
      · rw [Color.opponent_opponent, hL₀, F₀.neg_apply, add_assoc, add_neg_cancel, add_zero]
      · rw [Color.opponent_opponent, F₀.neg_dir, mem_halfPlaneDirections_swap_iff,
          mem_halfPlaneDirections_opposite]
        exact hs
      · rw [Color.opponent_opponent, mem_halfPlaneDirections_swap_iff,
          HalfPlaneSide.opposite_opposite]
        exact hsv₁
  obtain ⟨c, F, side, d, hL, hN, hd, hsd⟩ := start
  set K := kp 0 c
  set L := kp 0 c.opponent
  obtain ⟨hab, hu, hv, hNE, -, hW, hNW, q₁, hq₁⟩ := cand c side F a b hb hba ha hL hN d hd hsd
  -- The opposite half-plane, seen from the other king with the reflected frame.
  set both : Prop := ∃ d, tr.CheckingRay (kp 0 c) c d ∧
    d ∈ halfPlaneDirections K.toPlane L.toPlane side.opposite with hboth
  have hL' : (kp 0 c.opponent.opponent).toPlane =
      (kp 0 c.opponent).toPlane + F.neg.apply ((a : ℚ), (b : ℚ)) := by
    rw [Color.opponent_opponent, hL, F.neg_apply, add_assoc, add_neg_cancel, add_zero]
  have hN' : F.neg.dir .north ∈ halfPlaneDirections (kp 0 c.opponent).toPlane
      (kp 0 c.opponent.opponent).toPlane side := by
    rw [Color.opponent_opponent, F.neg_dir, mem_halfPlaneDirections_swap_iff,
      mem_halfPlaneDirections_opposite]
    exact hN
  have lower : both →
      (a = 3 ∧ b = 1) ∧
      (∀ d ∈ halfPlaneDirections K.toPlane L.toPlane side.opposite,
        tr.CheckingRay (kp 0 c) c d ↔ d = F.dir .east ∨ d = F.dir .southEast) ∧
      (∀ e ∈ halfPlaneDirections K.toPlane L.toPlane side.opposite,
        tr.CheckingRay (kp 0 c.opponent) c.opponent e ↔
          e = F.dir .south ∨ e = F.dir .southWest) ∧
      F.dir .east ∈ halfPlaneDirections K.toPlane L.toPlane side.opposite ∧
      F.dir .southEast ∈ halfPlaneDirections K.toPlane L.toPlane side.opposite ∧
      F.dir .south ∈ halfPlaneDirections K.toPlane L.toPlane side.opposite ∧
      F.dir .southWest ∈ halfPlaneDirections K.toPlane L.toPlane side.opposite := by
    rintro ⟨d', hd', hsd'⟩
    obtain ⟨_, _, v₁, _, _, _, _, _, _, hv', _, _, hsv₁, _, _⟩ := rank c side.opposite d' hd' hsd'
    have hsv₁' : v₁ ∈ halfPlaneDirections (kp 0 c.opponent).toPlane
        (kp 0 c.opponent.opponent).toPlane side := by
      rw [Color.opponent_opponent, mem_halfPlaneDirections_swap_iff]; exact hsv₁
    obtain ⟨hab', hu', hv'', hNE', hN'', hW', hNW', q₂, hq₂⟩ := cand c.opponent side F.neg a b
      hb hba ha hL' hN' v₁ ((hv' v₁ hsv₁).mpr (Or.inl rfl)) hsv₁'
    simp only [Color.opponent_opponent] at hu' hv'' hNE' hN'' hW' hNW'
    have conv (x : RayDirection) :
        x ∈ halfPlaneDirections (kp 0 c.opponent).toPlane (kp 0 c).toPlane side ↔
          x ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side.opposite :=
      mem_halfPlaneDirections_swap_iff _ _ _ _
    simp only [F.neg_dir, ← F.dir_opposite, conv] at hu' hv'' hNE' hN'' hW' hNW'
    simp only [RayDirection.opposite] at hu' hv'' hNE' hN'' hW' hNW'
    refine ⟨?_, fun d hd => hv'' d hd, fun e he => (hu' e he).trans or_comm, hW', hNW', hN'', hNE'⟩
    -- The crossings `K + F(0, a+b)` and `L - F(0, a+b) = K + F(a, -a)` are both on the board.
    have hdiff : q₁.toPlane = q₂.toPlane + F.apply (-(a : ℚ), 2 * a + b) := by
      rw [hq₁, hq₂, hL, F.neg_apply]
      obtain ⟨s', x', y'⟩ := F
      cases s' <;> cases x' <;> cases y' <;> ext <;> simp [LatticeFrame.apply] <;> ring
    have hbound := (abs_le_seven_of_frame hdiff).2
    rw [abs_le] at hbound
    have h7 : 2 * a + b ≤ 7 := by
      have h := hbound.2
      norm_num at h
      exact_mod_cast h
    omega
  refine ⟨c, F, a, b, both, hab, fun h => (lower h).1, hL, ?_, ?_⟩
  · intro d
    constructor
    · intro h
      obtain ⟨s, hs⟩ := exists_mem_halfPlaneDirections (offset c d h)
      rcases side_eq_or_opposite s side with rfl | rfl
      · rcases (hu d hs).mp h with h | h
        exacts [Or.inl h, Or.inr (Or.inl h)]
      · exact Or.inr (Or.inr ⟨⟨d, h, hs⟩, ((lower ⟨d, h, hs⟩).2.1 d hs).mp h⟩)
    · rintro (rfl | rfl | ⟨hb', h | h⟩)
      · exact (hu _ hNE).mpr (Or.inl rfl)
      · exact (hu _ hN).mpr (Or.inr rfl)
      · obtain ⟨-, hc', -, hE, -⟩ := lower hb'
        subst h; exact (hc' _ hE).mpr (Or.inl rfl)
      · obtain ⟨-, hc', -, -, hSE, -⟩ := lower hb'
        subst h; exact (hc' _ hSE).mpr (Or.inr rfl)
  · intro e
    constructor
    · intro h
      have hoff : rayOffset K.toPlane L.toPlane e ≠ 0 := by
        have := offset c.opponent e h
        rw [Color.opponent_opponent, rayOffset_swap, neg_ne_zero] at this
        exact this
      obtain ⟨s, hs⟩ := exists_mem_halfPlaneDirections hoff
      rcases side_eq_or_opposite s side with rfl | rfl
      · rcases (hv e hs).mp h with h | h
        exacts [Or.inl h, Or.inr (Or.inl h)]
      · -- A checking ray of the other king forces checking rays of `c` on this side.
        have hs' : e ∈ halfPlaneDirections (kp 0 c.opponent).toPlane
            (kp 0 c.opponent.opponent).toPlane side := by
          rw [Color.opponent_opponent, mem_halfPlaneDirections_swap_iff]; exact hs
        obtain ⟨_, _, w₁, _, _, _, _, _, _, hw, _, _, hsw₁, _, _⟩ := rank c.opponent side e h hs'
        simp only [Color.opponent_opponent] at hw hsw₁
        have hb' : both := ⟨w₁, (hw w₁ hsw₁).mpr (Or.inl rfl),
          (mem_halfPlaneDirections_swap_iff _ _ _ _).mp hsw₁⟩
        exact Or.inr (Or.inr ⟨hb', ((lower hb').2.2.1 e hs).mp h⟩)
    · rintro (rfl | rfl | ⟨hb', h | h⟩)
      · exact (hv _ hW).mpr (Or.inl rfl)
      · exact (hv _ hNW).mpr (Or.inr rfl)
      · obtain ⟨-, -, hc', -, -, hS, -⟩ := lower hb'
        subst h; exact (hc' _ hS).mpr (Or.inl rfl)
      · obtain ⟨-, -, hc', -, -, -, hSW⟩ := lower hb'
        subst h; exact (hc' _ hSW).mpr (Or.inr rfl)

end MPC.Chess.MoveTrace
