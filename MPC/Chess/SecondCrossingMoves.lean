import MPC.Chess.CheckerCrossingOrder

/-! Lemma 6.4(2): a checker at A₂ must depart during the period. The cyclic
stay before its first departure excludes replacement by an identical piece. -/

namespace MPC.Chess.MoveTrace

/-- A crossing strictly before A₂ is A₁, also for non-lattice points. -/
theorem crossing_before_second_eq_first (tr : MoveTrace) (kp : Color → Pos)
    (c : Color) (d : RayDirection) (h : 1 < (tr.rayCrossingParameters kp c d).card)
    (q : PlanePoint) (hm : q ∈ tr.checkingCrossings kp) (hr : OnRationalRay (kp c).toPlane d q)
    (hlt : rayParameter (kp c).toPlane d q <
      rayParameter (kp c).toPlane d (tr.secondCheckingCrossing kp c d h)) :
    q = tr.firstCheckingCrossing kp c d (by omega) := by
  by_contra hn
  exact (not_le_of_gt hlt) ((tr.secondCheckingCrossing_spec kp c d h).2.2.2 q hm hr hn)

/-- An occupied non-immovable square has a first departure in cyclic order.
The original piece contents persist, with no touches before that departure.
No checking, glare or king-placement premise is used. -/
theorem occupied_piece_departs_of_not_immovable (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (ho : tr.OrdinaryMoves) (k : Fin (tr.len + 1))
    (C : Pos) (X : Piece) (hX : (tr.states k).board C = some X) (hn : ¬ tr.ImmovableAt C) :
    ∃ (j : Fin tr.len) (dst : Pos), tr.moves j = .boardMove C dst none ∧
      (tr.before j).board C = some X ∧
      (∀ l, cyclicBetween k j.castSucc l → (tr.states l).board C = some X) ∧
      ∀ m, cyclicStepBetween k j.castSucc m → ¬ (tr.moves m).Touches (tr.before m).turn C := by
  have hex : ∃ m, (tr.moves m).Touches (tr.before m).turn C := by
    by_contra! hun
    have he := tr.board_eq_of_untouched hl C (Fin.zero_le k) (fun m _ _ => hun m)
    exact hn ⟨by rw [← he, hX]; exact Option.some_ne_none _, hun⟩
  have hocc : (tr.states k).board C ≠ none := by rw [hX]; exact Option.some_ne_none _
  suffices ∃ (j : Fin tr.len) (dst : Pos), tr.moves j = .boardMove C dst none ∧
      ∀ l, cyclicBetween k j.castSucc l → (tr.states l).board C = some X by
    obtain ⟨j, dst, hm, hall⟩ := this
    have hend : cyclicBetween k j.castSucc j.castSucc := by
      rcases le_or_gt k j.castSucc with h | h
      · exact Or.inl ⟨h, h, le_refl _⟩
      · exact Or.inr ⟨h, Or.inr (le_refl _)⟩
    refine ⟨j, dst, hm, hall _ hend, hall, ?_⟩
    intro m hstay
    obtain ⟨hb, ha⟩ := cyclicStepBetween_states hstay
    apply tr.not_touches_of_occupied_before_after hl hp ho m C
    · change (tr.states m.castSucc).board C ≠ none; rw [hall _ hb]; exact Option.some_ne_none _
    · change (tr.states m.succ).board C ≠ none; rw [hall _ ha]; exact Option.some_ne_none _
  by_cases hlater : ∃ m, k ≤ m.castSucc ∧ (tr.moves m).Touches (tr.before m).turn C
  · obtain ⟨j, dst, hkj, hm, hall⟩ := tr.departure_of_occupied_of_periodic hl hp ho C k hocc hlater
    refine ⟨j, dst, hm, ?_⟩
    intro l hstay
    obtain ⟨hkl, hlj⟩ := (cyclicBetween_iff_of_le l hkj).mp hstay
    exact (hall l hkl hlj).trans hX
  · push Not at hlater
    have hzero : (tr.states 0).board C = (tr.states k).board C := by
      rw [← hp.1]
      exact tr.board_eq_of_untouched hl C (Fin.le_last _) (fun m h₁ _ => hlater m h₁)
    obtain ⟨m, hm⟩ := hex
    obtain ⟨j, dst, _, hmj, hall⟩ := tr.departure_of_occupied_of_periodic hl hp ho C 0
      (by rw [hzero]; exact hocc) ⟨m, Fin.zero_le _, hm⟩
    have hjk : j.castSucc < k := by
      by_contra hn
      exact hlater j (le_of_not_gt hn) (by rw [hmj]; exact Or.inl rfl)
    refine ⟨j, dst, hmj, ?_⟩
    intro l hstay
    rcases hstay with ⟨hle, _, _⟩ | ⟨_, hkl | hlj⟩
    · exact (not_le_of_gt hjk hle).elim
    · exact (tr.board_eq_of_untouched hl C hkl (fun m h₁ _ => hlater m h₁)).trans hX
    · exact (hall l (Fin.zero_le _) hlj).trans (hzero.trans hX)

private theorem crossing_between_second (tr : MoveTrace) (kp : Color → Pos)
    (c : Color) (d : RayDirection) (h : 1 < (tr.rayCrossingParameters kp c d).card)
    (C A : Pos) (he : C.toPlane = tr.secondCheckingCrossing kp c d h)
    (hd : OnRay (kp c) d C) (hA : A.toPlane ∈ tr.checkingCrossings kp) (hb : Between C (kp c) A) :
    A.toPlane = tr.firstCheckingCrossing kp c d (by omega) := by
  have hrA := (onRationalRay_toPlane_iff _ _ _).mpr (Or.inr (hd.of_between hb))
  have hrC := (onRationalRay_toPlane_iff _ _ _).mpr (Or.inr hd)
  apply tr.crossing_before_second_eq_first kp c d h _ hA hrA
  rw [← he]
  apply (hrA.parameter_lt_iff_distance_lt hrC).mpr
  have hdist := (hd.between_iff_distance (hd.of_between hb)).mp hb
  unfold rayDistance at hdist
  unfold planeTaxicabDistance Pos.toPlane
  simp only
  exact_mod_cast hdist

private theorem checker_at_second_not_immovable_before (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (C : Pos) (X : Piece)
    (hX : (tr.before i).board C = some X) (ho : X.owner = (tr.before i).turn.opponent)
    (ha : attacks (tr.before i).board X C (kp i.castSucc (tr.before i).turn))
    (d : RayDirection) (hd : OnRay (kp 0 (tr.before i).turn) d C)
    (h : 1 < (tr.rayCrossingParameters (kp 0) (tr.before i).turn d).card)
    (he : C.toPlane = tr.secondCheckingCrossing (kp 0) (tr.before i).turn d h) :
    ¬ tr.ImmovableAt C := by
  intro himm
  have hkp := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hs := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp (Nat.zero_lt_of_lt i.isLt)
    i.castSucc (tr.before i).turn C X hX ho ha
  obtain ⟨src, A, hm⟩ := tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp i
  have hbA := tr.destination_between_checker_of_periodic_checks kp hl hk hc hp i src A C X hm hX ho ha
  have hA := (tr.boardMove_mem_checkingCrossings_of_periodic_checks kp hl hk hc hp i src A hm).2
  obtain ⟨j, dst, hmj, _, ht⟩ := tr.arrival_piece_departs_of_periodic hl hp
    (tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp) i src A hm
  have hXj : (tr.after j).board C = some X := (tr.immovable_board_eq hl C himm j.succ i.castSucc).trans hX
  rw [hkp i.castSucc 0] at ha
  have hnot : ¬ pathClear (tr.after j).board C (kp 0 (tr.before i).turn) := by
    intro hclear
    apply tr.ownKing_safe_after_of_legal kp hl hk j
    rw [hkp j.succ 0, ht]
    exact ⟨C, X, hXj, ho, attacks_of_pathClear _ _ X C _ ha hclear⟩
  unfold pathClear at hnot
  push Not at hnot
  obtain ⟨B, hbB, hocc⟩ := hnot
  have hBempty : (tr.before i).board B = none := by
    rcases hs with hs | hs | hs <;> simp only [attacks, hs] at ha <;> exact ha.2.2 B hbB
  have hB := tr.mem_checkingCrossings_of_board_ne kp hl hk hc hp B j.succ i.castSucc
    (by change (tr.after j).board B ≠ (tr.before i).board B; rwa [hBempty])
  have hAB : A = B := Pos.toPlane_injective
    ((tr.crossing_between_second (kp 0) _ d h C A he hd hA hbA).trans
      (tr.crossing_between_second (kp 0) _ d h C B he hd hB hbB).symm)
  obtain ⟨_, hv, hej⟩ := hl j
  have hv' : PseudoLegal (tr.before j) (.boardMove A dst none) := by simpa only [hmj] using hv.movement
  obtain ⟨_, _, _, hne, _⟩ := hv'
  apply hocc
  rw [← hAB, hej, hmj]
  exact Board.relocate_source _ _ _ _ hne

/-- A checker at A₂ is not an immovable occupied square. The two-crossing
cardinality is derived from the trace, and first/final states are both covered. -/
theorem checker_not_immovable_at_second_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) (k : Fin (tr.len + 1)) (C : Pos) (X : Piece)
    (hX : (tr.states k).board C = some X) (ho : X.owner = c.opponent)
    (ha : attacks (tr.states k).board X C (kp k c)) (hd : OnRay (kp 0 c) d C)
    (he : C.toPlane = tr.secondCheckingCrossing (kp 0) c d
      (tr.rayCrossingParameters_card_two_le_of_periodic_checks kp hl hk hc hp hn c d hr)) :
    ¬ tr.ImmovableAt C := by
  by_cases ht : c = (tr.states k).turn
  · subst c
    revert hX ho ha hd he hr
    refine Fin.lastCases ?_ (fun i hX hr ho ha hd he => ?_) k
    · intro hX hr ho ha hd he
      let first : Fin tr.len := ⟨0, hn⟩
      rw [hp.1] at hX ha
      rw [hp.2] at ho ha hd
      simp only [hp.2] at he
      rw [tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp (Fin.last tr.len) 0] at ha
      exact tr.checker_at_second_not_immovable_before kp hl hk hc hp first C X hX ho ha d hd _ he
    · exact tr.checker_at_second_not_immovable_before kp hl hk hc hp i C X hX ho ha d hd _ he
  · have ht' : c = (tr.states k).turn.opponent := by
      cases c <;> cases ht'' : (tr.states k).turn <;> simp_all [Color.opponent]
    subst c
    exact (tr.opponent_safe_of_periodic kp hl hk hp hn k ⟨C, X, hX, ho, ha⟩).elim

/-- Paper Lemma 6.4(2), with a concrete ordinary departure of the original
checker after an untouched cyclic stay. No piece identities are introduced. -/
theorem checker_at_second_departs_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) (k : Fin (tr.len + 1)) (C : Pos) (X : Piece)
    (hX : (tr.states k).board C = some X) (ho : X.owner = c.opponent)
    (ha : attacks (tr.states k).board X C (kp k c)) (hd : OnRay (kp 0 c) d C)
    (he : C.toPlane = tr.secondCheckingCrossing (kp 0) c d
      (tr.rayCrossingParameters_card_two_le_of_periodic_checks kp hl hk hc hp hn c d hr)) :
    ∃ (j : Fin tr.len) (dst : Pos), tr.moves j = .boardMove C dst none ∧
      (tr.before j).board C = some X ∧
      (∀ l, cyclicBetween k j.castSucc l → (tr.states l).board C = some X) ∧
      ∀ m, cyclicStepBetween k j.castSucc m → ¬ (tr.moves m).Touches (tr.before m).turn C := by
  exact tr.occupied_piece_departs_of_not_immovable hl hp
    (tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp) k C X hX
    (tr.checker_not_immovable_at_second_of_periodic_checks kp hl hk hc hp hn c d hr k C X hX ho ha hd he)

end MPC.Chess.MoveTrace
