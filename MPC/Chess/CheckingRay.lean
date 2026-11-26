import MPC.Chess.OpenableLineCyclic
import MPC.Chess.CheckingRayGeometry

/-! Definition 6.1: an actual enemy checker occurs on the ray at some state.
The origin is supplied explicitly; applications derive its constancy from
periodic legal mutual checks. Glare alone is not a checking-ray witness. -/

namespace MPC.Chess.MoveTrace

def CheckingRay (tr : MoveTrace) (king : Pos) (owner : Color) (d : RayDirection) : Prop :=
  ∃ k q p, (tr.states k).board q = some p ∧ p.owner = owner.opponent ∧
    attacks (tr.states k).board p q king ∧ OnRay king d q

instance (tr : MoveTrace) (king : Pos) (owner : Color) (d : RayDirection) :
    Decidable (tr.CheckingRay king owner d) :=
  inferInstanceAs (Decidable (∃ k q p, (tr.states k).board q = some p ∧
    p.owner = owner.opponent ∧ attacks (tr.states k).board p q king ∧ OnRay king d q))

theorem exists_checkingRay_of_slider (tr : MoveTrace) (k : Fin (tr.len + 1))
    (king q : Pos) (owner : Color) (p : Piece) (hp : (tr.states k).board q = some p)
    (ho : p.owner = owner.opponent) (hs : p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop)
    (ha : attacks (tr.states k).board p q king) :
    ∃ d, tr.CheckingRay king owner d ∧ OnRay king d q := by
  obtain ⟨d, hd⟩ := exists_onRay_of_aligned (attacks_aligned_of_slider hs ha) ha.1
  exact ⟨d, ⟨k, q, p, hp, ho, ha, hd⟩, hd⟩

/-- Recurrence forces every departing square to be a destination somewhere in
the trace. The corresponding arrival may precede or follow the selected move. -/
theorem source_is_destination_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (ho : tr.OrdinaryMoves) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    ∃ (j : Fin tr.len) (a : Pos), tr.moves j = .boardMove a src none := by
  classical
  by_contra hn
  have hd (j : Fin tr.len) (a b : Pos) (hj : tr.moves j = .boardMove a b none) : b ≠ src :=
    fun h => hn ⟨j, a, h ▸ hj⟩
  let f (k : Fin (tr.len + 1)) : ℕ := if (tr.states k).board src = none then 0 else 1
  have hstep (j : Fin tr.len) : f j.succ ≤ f j.castSucc := by
    obtain ⟨a, b, hj⟩ := ho j
    obtain ⟨_, _, he⟩ := hl j
    have hbs := hd j a b hj
    change (if (tr.after j).board src = none then 0 else 1) ≤ _
    rw [he, hj]
    simp only [applyMove, applyBoard, Board.relocate, Ne.symm hbs, ite_false]
    unfold f
    split_ifs <;> simp_all [before]
  have hmono : Antitone f := Fin.antitone_iff_succ_le.mpr hstep
  have hperiod : f (Fin.last tr.len) = f 0 := by simp only [f, hp.1]
  have hconst (k : Fin (tr.len + 1)) : f k = f 0 := by
    have h₁ := hmono (Fin.zero_le k)
    have h₂ := hmono (Fin.le_last k)
    rw [hperiod] at h₂; omega
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by simpa only [hm] using hv.movement
  obtain ⟨p, hs, _, hne, _⟩ := hv'
  have hempty : (tr.after i).board src = none := by
    rw [he, hm]; exact Board.relocate_source _ _ _ _ hne
  have hf := (hconst i.succ).trans (hconst i.castSucc).symm
  change (if (tr.after i).board src = none then 0 else 1) =
    (if (tr.before i).board src = none then 0 else 1) at hf
  simp [hempty, hs] at hf

private theorem destination_enemy_ray (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    ∃ d, tr.CheckingRay (kp 0 (tr.before i).turn.opponent) (tr.before i).turn.opponent d ∧
      OnRay (kp 0 (tr.before i).turn.opponent) d dst := by
  have hkp := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hlen : 0 < tr.len := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  by_cases hg : tr.GlaresAtEnemyKing kp i.succ dst
  · obtain ⟨p, hs, ho, ha⟩ := tr.destinationChecker_of_source_glares kp hl hk hc hp i src dst hm
      (tr.glares_source_of_destination_of_periodic_checks kp hl hk hc hp i src dst hm hg)
    have hslider := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp hlen
      i.succ (tr.before i).turn.opponent dst p hs ho ha
    rw [hkp i.succ 0] at ha
    exact tr.exists_checkingRay_of_slider i.succ _ dst _ p hs ho hslider ha
  · obtain ⟨j, a, B, Q, hmj, _, _, _, hall, _⟩ :=
      tr.openable_line_cyclic_of_periodic_checks kp hl hk hc hp i src dst hm hg
    have hstay : cyclicBetween i.succ j.castSucc j.castSucc := by
      unfold cyclicBetween; rcases le_or_gt i.succ j.castSucc with h | h
      · exact Or.inl ⟨h, h, le_refl _⟩
      · exact Or.inr ⟨h, Or.inr (le_refl _)⟩
    have hb := (hall j.castSucc hstay).1
    have hngj : ¬ tr.GlaresAtEnemyKing kp j.castSucc dst := fun h =>
      hg ((tr.glares_congr kp hl hb (hkp _ _)).mp h)
    obtain ⟨C, X, _, _, hX0, hX1, hXo, _, ha, hbetween, _⟩ :=
      (tr.unblockedChecker_iff_not_source_glares_of_periodic_checks kp hl hk hc hp j dst a hmj).mpr hngj
    obtain ⟨_, hv, he⟩ := hl i
    have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by simpa only [hm] using hv.movement
    obtain ⟨p, hs, ho, _⟩ := hv'
    have hpd : (tr.states i.succ).board dst = some p := by
      change (tr.after i).board dst = some p
      rw [he, hm]; simp [applyMove, applyBoard, hs, Piece.promote]
    obtain ⟨_, hj, _⟩ := hl j
    have hj' : PseudoLegal (tr.before j) (.boardMove dst a none) := by simpa only [hmj] using hj.movement
    obtain ⟨p', hs', ho', _⟩ := hj'
    change (tr.states j.castSucc).board dst = some p' at hs'
    rw [hb, hpd] at hs'
    have hp' : p = p' := Option.some.inj hs'
    have hturn : (tr.before j).turn = (tr.before i).turn := by rw [← ho', ← hp', ho]
    have hslider := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp hlen
      j.succ (tr.before j).turn.opponent C X hX1 hXo ha
    rw [hkp j.succ 0, hturn] at ha hbetween
    rw [hturn] at hXo
    obtain ⟨d, hd, hr⟩ := tr.exists_checkingRay_of_slider j.succ _ C _ X hX1 hXo hslider ha
    exact ⟨d, hd, hr.of_between hbetween⟩

/-- Both kings' checking rays contain the destination. For a non-glaring
mover, the enemy ray is witnessed by the later departure, not merely by glare. -/
theorem destination_on_checkingRay_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) (owner : Color) :
    ∃ d, tr.CheckingRay (kp 0 owner) owner d ∧ OnRay (kp 0 owner) d dst := by
  by_cases ho : owner = (tr.before i).turn.opponent
  · subst owner; exact tr.destination_enemy_ray kp hl hk hc hp i src dst hm
  have ho' : owner = (tr.before i).turn := by
    cases owner <;> cases ht : (tr.before i).turn <;> simp_all [Color.opponent]
  subst owner
  have hlen : 0 < tr.len := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨C, X, hs, hXo, hslider, ha⟩ :=
    tr.exists_slider_checker_of_periodic_checks kp hl hk hc hp hlen i.castSucc
  have hbetween := tr.destination_between_checker_of_periodic_checks kp hl hk hc hp i src dst C X hm hs hXo ha
  rw [tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp i.castSucc 0] at ha
  obtain ⟨d, hd, hr⟩ := tr.exists_checkingRay_of_slider i.castSucc _ C _ X hs hXo hslider ha
  exact ⟨d, hd, hr.of_between hbetween⟩

theorem source_on_checkingRay_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) (owner : Color) :
    ∃ d, tr.CheckingRay (kp 0 owner) owner d ∧ OnRay (kp 0 owner) d src := by
  obtain ⟨j, a, hj⟩ := tr.source_is_destination_of_periodic hl hp
    (tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp) i src dst hm
  exact tr.destination_on_checkingRay_of_periodic_checks kp hl hk hc hp j a src hj owner

end MPC.Chess.MoveTrace
