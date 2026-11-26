import MPC.Chess.Figure3Moves
import MPC.Chess.SecondCrossingMoves

/-! The lower candidate of Figure 3 and the main theorem. With the kings at `K`
and `L = K + F(3, 1)` and checking rays in both half-planes, the crossings on
the ray `LC` (the canonical south from `L`) are `K + F(3, 0)` and
`C = K + F(3, -3)`, and the board ends at `C`. A checker on `LC` therefore
stands on `C`, the second crossing, and by Lemma 6.4(2) leaves it. By Lemma 6.2
it must move to a crossing on other rays of both kings, and none of them is a
line move or a knight jump away from `C`. -/

namespace MPC.Chess

open LatticeFrame

theorem frame_rational_crossing_eq {K L p : PlanePoint} {F : LatticeFrame} {w : PlanePoint}
    (hL : L = K + F.apply w) {dk dl : RayDirection}
    (h₁ : OnRationalRay K (F.dir dk) p) (h₂ : OnRationalRay L (F.dir dl) p) :
    ∃ t s : ℚ, 0 ≤ t ∧ 0 ≤ s ∧ p = K + F.apply (rayPoint (0, 0) dk t) ∧
      rayPoint (0, 0) dk t = w + rayPoint (0, 0) dl s := by
  obtain ⟨t, ht, e₁⟩ := (onRationalRay_dir_iff K p F dk).mp h₁
  obtain ⟨s, hs, e₂⟩ := (onRationalRay_dir_iff L p F dl).mp h₂
  refine ⟨t, s, ht, hs, e₁, F.apply_injective ?_⟩
  rw [F.apply_add]
  have h := e₁.symm.trans e₂
  rw [hL, add_assoc] at h
  exact add_left_cancel h

/-- Solves the canonical crossing equation of two concrete rays. -/
local macro "cross_tac" : tactic => `(tactic|
  (simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at *
   norm_num at * <;> first | linarith | (obtain ⟨_, _⟩ := ‹_ ∧ _›; linarith)))

section LowerCrossings

variable {K L q : Pos} {F : LatticeFrame}

theorem crossing_east_southWest (hL : L.toPlane = K.toPlane + F.apply (3, 1))
    (h₁ : OnRay K (F.dir .east) q) (h₂ : OnRay L (F.dir .southWest) q) :
    q.toPlane = K.toPlane + F.apply (2, 0) := by
  obtain ⟨t, s, -, -, hq, he⟩ := frame_crossing_eq hL h₁ h₂
  simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he
  norm_num at he
  rw [hq]; congr 2; simp only [rayPoint, RayDirection.vector]; ext <;> norm_num; linarith

theorem not_crossing_northEast_southWest (hL : L.toPlane = K.toPlane + F.apply (3, 1)) :
    ¬ (OnRay K (F.dir .northEast) q ∧ OnRay L (F.dir .southWest) q) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨t, s, ht, hs, -, he⟩ := frame_crossing_eq hL h₁ h₂
  cross_tac

theorem not_crossing_north_southWest (hL : L.toPlane = K.toPlane + F.apply (3, 1)) :
    ¬ (OnRay K (F.dir .north) q ∧ OnRay L (F.dir .southWest) q) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨t, s, ht, hs, -, he⟩ := frame_crossing_eq hL h₁ h₂
  cross_tac

theorem not_crossing_north_south (hL : L.toPlane = K.toPlane + F.apply (3, 1)) :
    ¬ (OnRay K (F.dir .north) q ∧ OnRay L (F.dir .south) q) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨t, s, ht, hs, -, he⟩ := frame_crossing_eq hL h₁ h₂
  cross_tac

theorem not_crossing_east_west (hL : L.toPlane = K.toPlane + F.apply (3, 1)) :
    ¬ (OnRay K (F.dir .east) q ∧ OnRay L (F.dir .west) q) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨t, s, ht, hs, -, he⟩ := frame_crossing_eq hL h₁ h₂
  cross_tac

theorem not_crossing_east_northWest (hL : L.toPlane = K.toPlane + F.apply (3, 1)) :
    ¬ (OnRay K (F.dir .east) q ∧ OnRay L (F.dir .northWest) q) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨t, s, ht, hs, -, he⟩ := frame_crossing_eq hL h₁ h₂
  cross_tac

end LowerCrossings

/-- The rational crossings on the ray `LC` of the lower candidate are at
parameters 1 and 4 from `L`. -/
theorem lowerRay_crossing_parameter {K L : PlanePoint} {F : LatticeFrame} {p : PlanePoint}
    (hL : L = K + F.apply (3, 1)) {m : RayDirection}
    (hm : m = .northEast ∨ m = .north ∨ m = .east ∨ m = .southEast)
    (h₁ : OnRationalRay K (F.dir m) p) (h₂ : OnRationalRay L (F.dir .south) p) :
    p = rayPoint L (F.dir .south) 1 ∨ p = rayPoint L (F.dir .south) 4 := by
  obtain ⟨t, ht, e₁⟩ := (onRationalRay_dir_iff K p F m).mp h₁
  obtain ⟨s, hs, e₂⟩ := (onRationalRay_dir_iff L p F .south).mp h₂
  have he : rayPoint (0, 0) m t = (3, 1) + rayPoint (0, 0) .south s := by
    apply F.apply_injective
    rw [F.apply_add]
    have h := e₁.symm.trans e₂
    rw [hL, add_assoc] at h
    exact add_left_cancel h
  have hp : p = rayPoint L (F.dir .south) s := by rw [rayPoint_dir]; exact e₂
  rcases hm with rfl | rfl | rfl | rfl <;>
    simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he <;>
    norm_num at he
  · exfalso; linarith [he.1, he.2]
  · left; rw [hp, show s = 1 by linarith]
  · right; rw [hp, show s = 4 by linarith [he.1, he.2]]

namespace MoveTrace

set_option maxHeartbeats 1000000 in
/-- The lower candidate of Figure 3 is impossible: the checker on `LC` stands
on `C`, the second crossing, must leave it by Lemma 6.4(2), and has no square
to go to under Lemma 6.2. -/
theorem false_of_lower_candidate (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (F : LatticeFrame)
    (hL : (kp 0 c.opponent).toPlane = (kp 0 c).toPlane + F.apply (3, 1))
    (hu : ∀ d, tr.CheckingRay (kp 0 c) c d ↔ d = F.dir .northEast ∨ d = F.dir .north ∨
      d = F.dir .east ∨ d = F.dir .southEast)
    (hv : ∀ e, tr.CheckingRay (kp 0 c.opponent) c.opponent e ↔ e = F.dir .west ∨
      e = F.dir .northWest ∨ e = F.dir .south ∨ e = F.dir .southWest) : False := by
  have hne := tr.checkingCrossing_ne_king_of_periodic_checks kp hl hk hc hp hn
  -- A crossing on a ray of `c` lies on a checking ray of the other king.
  have other (X : Pos) (hX : X.toPlane ∈ tr.checkingCrossings (kp 0)) :
      ∃ e, tr.CheckingRay (kp 0 c.opponent) c.opponent e ∧ OnRay (kp 0 c.opponent) e X := by
    have hx := tr.checkingCrossing_of_mem_checkingCrossings _ _ hX
    obtain ⟨e, he, heX⟩ := hx c.opponent
    refine ⟨e, he, ((onRationalRay_toPlane_iff _ _ _).mp heX).resolve_left fun h => ?_⟩
    exact hne _ hx c.opponent (congrArg Pos.toPlane h)
  -- A board square at canonical height 4: the farther crossing on the canonical north.
  obtain ⟨T, hT⟩ : ∃ T : Pos, T.toPlane = (kp 0 c).toPlane + F.apply (0, 4) := by
    obtain ⟨A, B, hAB, hA, hB, hKA, hKB⟩ := tr.checkingRay_two_crossings_of_periodic_checks
      kp hl hk hc hp hn c (F.dir .north) ((hu _).mpr (by simp))
    have pos (X : Pos) (hX : X.toPlane ∈ tr.checkingCrossings (kp 0))
        (hKX : OnRay (kp 0 c) (F.dir .north) X) :
        X.toPlane = (kp 0 c).toPlane + F.apply (0, 1) ∨
          X.toPlane = (kp 0 c).toPlane + F.apply (0, 4) := by
      obtain ⟨e, he, hLX⟩ := other X hX
      rcases (hv e).mp he with rfl | rfl | rfl | rfl
      · left; rw [crossing_north_west hL hKX hLX]
      · right; rw [crossing_north_northWest hL hKX hLX]; norm_num
      · exact absurd ⟨hKX, hLX⟩ (not_crossing_north_south hL)
      · exact absurd ⟨hKX, hLX⟩ (not_crossing_north_southWest hL)
    rcases pos A hA hKA with h₁ | h₁ <;> rcases pos B hB hKB with h₂ | h₂
    · exact absurd (Pos.toPlane_injective (h₁.trans h₂.symm)) hAB
    · exact ⟨B, h₂⟩
    · exact ⟨A, h₁⟩
    · exact ⟨A, h₁⟩
  -- The checking ray `LC` and a checker on it.
  have hS : tr.CheckingRay (kp 0 c.opponent) c.opponent (F.dir .south) := (hv _).mpr (by simp)
  obtain ⟨k, q, X, hX, ho, ha, hq⟩ := hS
  have ha' : attacks (tr.states k).board X q (kp k c.opponent) := by
    rwa [tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp k 0]
  obtain ⟨t, ht, hqt⟩ := (onRay_dir_iff _ _ _ _).mp hq
  have hqK : q.toPlane = (kp 0 c).toPlane + F.apply (3, 1 - t) := by
    rw [hqt, hL, add_assoc, ← F.apply_add]
    congr 2
    ext <;> simp [rayPoint, RayDirection.vector]; ring
  -- The board ends at `C`: parameter at most 4.
  have hle : t ≤ 4 := by
    have hTq : T.toPlane = q.toPlane + F.apply (-3, 3 + t) := by
      rw [hT, hqK, add_assoc, ← F.apply_add]
      congr 2
      ext <;> norm_num
    have := (abs_le_seven_of_frame hTq).2
    rw [abs_le] at this
    simp only at this
    linarith [this.2]
  -- The second crossing on `LC` is `C`, at parameter 4.
  have h2 := tr.rayCrossingParameters_card_two_le_of_periodic_checks kp hl hk hc hp hn
    c.opponent (F.dir .south) ((hv _).mpr (by simp))
  have hcls (p : PlanePoint) (hp' : p ∈ tr.checkingCrossings (kp 0))
      (hr : OnRationalRay (kp 0 c.opponent).toPlane (F.dir .south) p) :
      p = rayPoint (kp 0 c.opponent).toPlane (F.dir .south) 1 ∨
        p = rayPoint (kp 0 c.opponent).toPlane (F.dir .south) 4 := by
    obtain ⟨d, hd, hdp⟩ := (tr.checkingCrossing_of_mem_checkingCrossings _ _ hp') c
    have hm : ∃ m, d = F.dir m ∧ (m = .northEast ∨ m = .north ∨ m = .east ∨ m = .southEast) := by
      rcases (hu d).mp hd with rfl | rfl | rfl | rfl
      exacts [⟨_, rfl, Or.inl rfl⟩, ⟨_, rfl, Or.inr (Or.inl rfl)⟩,
        ⟨_, rfl, Or.inr (Or.inr (Or.inl rfl))⟩, ⟨_, rfl, Or.inr (Or.inr (Or.inr rfl))⟩]
    obtain ⟨m, rfl, hm⟩ := hm
    exact lowerRay_crossing_parameter hL hm hdp hr
  have hparam (s : ℚ) :
      rayParameter (kp 0 c.opponent).toPlane (F.dir .south)
        (rayPoint (kp 0 c.opponent).toPlane (F.dir .south) s) = s := rayParameter_rayPoint _ _ _
  have hA₂C : tr.secondCheckingCrossing (kp 0) c.opponent (F.dir .south) h2 =
      rayPoint (kp 0 c.opponent).toPlane (F.dir .south) 4 := by
    obtain ⟨hmem₂, hon₂, hlt, -⟩ :=
      tr.secondCheckingCrossing_spec (kp 0) c.opponent (F.dir .south) h2
    obtain ⟨hmem₁, hon₁, -⟩ := tr.firstCheckingCrossing_spec (kp 0) c.opponent (F.dir .south)
      (by omega)
    rcases hcls _ hmem₂ hon₂ with h | h
    · exfalso
      rcases hcls _ hmem₁ hon₁ with h' | h' <;> simp only [h, h', hparam] at hlt <;>
        norm_num at hlt
    · exact h
  have hge := tr.checker_parameter_ge_second_of_periodic_checks kp hl hk hc hp hn c.opponent
    (F.dir .south) ((hv _).mpr (by simp)) k q X hX ho ha' hq
  rw [hA₂C, hparam] at hge
  have hqpt : q.toPlane = rayPoint (kp 0 c.opponent).toPlane (F.dir .south) t := by
    rw [rayPoint_dir]; exact hqt
  rw [hqpt, hparam] at hge
  have ht4 : t = 4 := le_antisymm hle hge
  subst ht4
  -- The checker leaves `C` (Lemma 6.4(2)).
  obtain ⟨j, dst, hmj, -⟩ := tr.checker_at_second_departs_of_periodic_checks kp hl hk hc hp hn
    c.opponent (F.dir .south) ((hv _).mpr (by simp)) k q X hX ho ha' hq
    (by rw [hqpt]; exact hA₂C.symm)
  -- Lemma 6.2 for that move, and the step shape.
  obtain ⟨src, dst', hm', hr⟩ := tr.every_move_between_distinct_checkingRays kp hl hk hc hp j
  rw [hmj] at hm'
  obtain ⟨hsrc, hdst, -⟩ := Move.boardMove.inj hm'
  subst hsrc hdst
  have hstep := tr.move_stepShape_of_periodic_checks kp hl hk hc hp j q dst hmj
  obtain ⟨ds, dd, hne₁, -, hdd, hsK, hdK⟩ := hr c
  obtain ⟨es, ed, hne₂, -, hed, hsL, hdL⟩ := hr c.opponent
  have hqC : q.toPlane = (kp 0 c).toPlane + F.apply (3, -3) := by rw [hqK]; norm_num
  have hSE : OnRay (kp 0 c) (F.dir .southEast) q := (onRay_dir_iff _ _ _ _).mpr
    ⟨3, by norm_num, by
      rw [hqC]; congr 2; simp only [rayPoint, RayDirection.vector]; ext <;> norm_num⟩
  have hds : ds = F.dir .southEast := OnRay.direction_unique hsK hSE
  have hes : es = F.dir .south := OnRay.direction_unique hsL hq
  subst hds hes
  have shape (x y : ℚ) (hd : dst.toPlane = (kp 0 c).toPlane + F.apply (x, y)) :
      StepShape (x - 3) (y - -3) := stepShape_canonical hqC hd hstep
  have hdd' : dd = F.dir .northEast ∨ dd = F.dir .north ∨ dd = F.dir .east := by
    rcases (hu dd).mp hdd with h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h), absurd h.symm hne₁]
  have hed' : ed = F.dir .west ∨ ed = F.dir .northWest ∨ ed = F.dir .southWest := by
    rcases (hv ed).mp hed with h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), absurd h.symm hne₂, Or.inr (Or.inr h)]
  rcases hdd' with rfl | rfl | rfl <;> rcases hed' with rfl | rfl | rfl
  · have := shape _ _ (crossing_northEast_west hL hdK hdL)
    norm_num [StepShape] at this
  · have := shape _ _ (crossing_northEast_northWest hL hdK hdL)
    norm_num [StepShape] at this
  · exact not_crossing_northEast_southWest hL ⟨hdK, hdL⟩
  · have := shape _ _ (crossing_north_west hL hdK hdL)
    norm_num [StepShape] at this
  · have := shape _ _ (crossing_north_northWest hL hdK hdL)
    norm_num [StepShape] at this
  · exact not_crossing_north_southWest hL ⟨hdK, hdL⟩
  · exact not_crossing_east_west hL ⟨hdK, hdL⟩
  · exact not_crossing_east_northWest hL ⟨hdK, hdL⟩
  · have := shape _ _ (crossing_east_southWest hL hdK hdL)
    norm_num [StepShape] at this

end MoveTrace

/-- Section 6 of the paper for standard chess: no legal move sequence of
positive length checks the opponent's king with every move and returns to its
initial board and side to move. The kings' fixity, the absence of captures and
pawn moves, and all checking-ray, crossing and Figure 3 properties are derived,
not assumed. Castling rights and en-passant targets may differ at the end. -/
theorem mutual_perpetual_check_impossible :
    ¬ ∃ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos),
      0 < tr.len ∧ tr.FollowsLegalMoves ∧ tr.KingsWellPlaced kp ∧
        tr.EveryMoveChecksOpponent kp ∧ tr.BoardTurnPeriodic := by
  rintro ⟨tr, kp, hn, hl, hk, hc, hp⟩
  obtain ⟨c, F, hL, hu, hv⟩ := tr.figure3_lower_candidate_of_periodic_checks kp hl hk hc hp hn
  exact tr.false_of_lower_candidate kp hl hk hc hp hn c F hL hu hv

end MPC.Chess
