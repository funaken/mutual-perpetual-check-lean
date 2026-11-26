import MPC.Chess.CheckingRay

/-! Lemma 6.2: every move joins distinct checking rays of each king.
Ray membership and distinctness are proved separately: the latter uses actual
clear paths and empty destinations, not a classification assumption. -/

namespace MPC.Chess.MoveTrace

/-- A move cannot remain on one queen ray of either king. This conclusion
holds independently of whether that ray has yet been classified as checking. -/
theorem not_same_ray_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) (owner : Color) (d : RayDirection) :
    ¬ (OnRay (kp 0 owner) d src ∧ OnRay (kp 0 owner) d dst) := by
  rintro ⟨hrs, hrd⟩
  obtain ⟨s, t, p, hm', hs, ho, hnk, hnp, hne, hempty, hmove⟩ :=
    tr.ordinary_nonKing_nonPawn_move_of_periodic_checks kp hl hk hc hp i
  have hes : s = src := (Move.boardMove.inj (hm'.symm.trans hm)).1
  have het : t = dst := (Move.boardMove.inj (hm'.symm.trans hm)).2.1
  subst s; subst t
  have hpath := pathClear_of_attack_onRay hrs hrd hnk hnp hmove
  have hkp := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hlen : 0 < tr.len := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨_, _, he⟩ := hl i
  have hboard : (tr.after i).board = (tr.before i).board.relocate src dst none := by
    rw [he, hm]; rfl
  by_cases howner : owner = (tr.before i).turn
  · subst owner
    obtain ⟨C, X, hX, hXo, hslider, ha⟩ :=
      tr.exists_slider_checker_of_periodic_checks kp hl hk hc hp hlen i.castSucc
    have hbetween := tr.destination_between_checker_of_periodic_checks kp hl hk hc hp i src dst C X hm hX hXo ha
    rw [hkp i.castSucc 0] at ha
    have hclear : pathClear (tr.before i).board C (kp 0 (tr.before i).turn) := by
      rcases hslider with h | h | h <;> simp only [attacks, h] at ha <;> exact ha.2.2
    have hn : ¬ Between C (kp 0 (tr.before i).turn) src := by
      intro h; have hz := hclear src h; rw [hs] at hz; contradiction
    have hsrc : src ≠ C := by
      intro h; subst C
      have hXp : X = p := Option.some.inj (hX.symm.trans hs)
      rw [hXp, ho] at hXo
      exact (tr.before i).turn.opponent_ne hXo.symm
    have hx := between_of_same_ray_exit hrd hrs (attacks_aligned_of_slider hslider ha) ha.1 hbetween hn hsrc
    have hz := hpath C hx.symm
    change (tr.before i).board C = some X at hX
    rw [hX] at hz; contradiction
  · have howner' : owner = (tr.before i).turn.opponent := by
      cases owner <;> cases ht : (tr.before i).turn <;> simp_all [Color.opponent]
    subst owner
    rcases tr.destination_or_unblocked_of_periodic_checks kp hl hk hc hp i src dst hm with hd | hu
    · obtain ⟨q, hq, hqo, ha⟩ := hd
      have hpd : (tr.after i).board dst = some p := by rw [hboard]; simp [hs, Piece.promote]
      have hqp : q = p := Option.some.inj (hq.symm.trans hpd)
      subst q
      have hslider := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp
        hlen i.succ (tr.before i).turn.opponent dst p hpd hqo ha
      rw [hkp i.succ 0] at ha
      have hclear : pathClear (tr.after i).board dst (kp 0 (tr.before i).turn.opponent) := by
        rcases hslider with h | h | h <;> simp only [attacks, h] at ha <;> exact ha.2.2
      rw [hboard] at hclear
      have hsource := pathClear_source_of_move_onRay hrs hrd hempty hpath hclear
      have hat := slider_attack_onRay hrd hrs hslider ha hsource
      have hsafe := tr.opponent_safe_of_periodic kp hl hk hp hlen i.castSucc
      rw [hkp i.castSucc 0] at hsafe
      exact hsafe ⟨src, p, hs, by simpa [MoveTrace.before] using ho, hat⟩
    · obtain ⟨C, X, _, hCd, hX, hXa, hXo, _, ha, hbetween, hn⟩ := hu
      have hslider := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp
        hlen i.succ (tr.before i).turn.opponent C X hXa hXo ha
      rw [hkp i.succ 0] at ha hbetween hn
      have hx := between_of_same_ray_exit hrs hrd (attacks_aligned_of_slider hslider ha) ha.1 hbetween hn hCd.symm
      have hz := hpath C hx
      rw [hX] at hz; contradiction

/-- Lemma 6.2 for a specified ordinary move and either king. The two rays
are witnessed by actual checks at possibly different states of the period. -/
theorem boardMove_between_distinct_checkingRays (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) (owner : Color) :
    ∃ ds dd, ds ≠ dd ∧ tr.CheckingRay (kp 0 owner) owner ds ∧
      tr.CheckingRay (kp 0 owner) owner dd ∧ OnRay (kp 0 owner) ds src ∧ OnRay (kp 0 owner) dd dst := by
  obtain ⟨ds, hs, hrs⟩ := tr.source_on_checkingRay_of_periodic_checks kp hl hk hc hp i src dst hm owner
  obtain ⟨dd, hd, hrd⟩ := tr.destination_on_checkingRay_of_periodic_checks kp hl hk hc hp i src dst hm owner
  refine ⟨ds, dd, ?_, hs, hd, hrs, hrd⟩
  intro h; subst dd
  exact tr.not_same_ray_of_periodic_checks kp hl hk hc hp i src dst hm owner ds ⟨hrs, hrd⟩

/-- All move constructors are covered: periodic legal mutual checks first
exclude special moves, promotion and pawn/king moves, then supply Lemma 6.2. -/
theorem every_move_between_distinct_checkingRays (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) :
    ∃ src dst, tr.moves i = .boardMove src dst none ∧ ∀ owner : Color,
      ∃ ds dd, ds ≠ dd ∧ tr.CheckingRay (kp 0 owner) owner ds ∧
        tr.CheckingRay (kp 0 owner) owner dd ∧ OnRay (kp 0 owner) ds src ∧ OnRay (kp 0 owner) dd dst := by
  obtain ⟨src, dst, hm⟩ := tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp i
  exact ⟨src, dst, hm, fun owner => tr.boardMove_between_distinct_checkingRays kp hl hk hc hp i src dst hm owner⟩

end MPC.Chess.MoveTrace
