import MPC.Chess.OpenableLine

/-! Proposition 3.3 across the periodic boundary. A first departure is derived
from the next touch of an occupied square. With no captures, that touch must be
a departure. The witness from its unblocked check persists back to the arrival,
including a stay that wraps from the final state to state zero. -/

namespace MPC.Chess

/-- Closed cyclic interval of states; the first and last states represent the
same board at the period boundary. Equality of endpoints denotes a single state. -/
def cyclicBetween {n : ℕ} (a b k : Fin (n + 1)) : Prop :=
  (a ≤ b ∧ a ≤ k ∧ k ≤ b) ∨ (b < a ∧ (a ≤ k ∨ k ≤ b))

/-- Moves inside the cyclic stay. This excludes the departure even when the
stay contains every state index: requiring both endpoints alone would not. -/
def cyclicStepBetween {n : ℕ} (a b : Fin (n + 1)) (m : Fin n) : Prop :=
  (a ≤ b ∧ a ≤ m.castSucc ∧ m.succ ≤ b) ∨
    (b < a ∧ (a ≤ m.castSucc ∨ m.succ ≤ b))

instance {n : ℕ} (a b k : Fin (n + 1)) : Decidable (cyclicBetween a b k) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ (_ ∨ _))))

instance {n : ℕ} (a b : Fin (n + 1)) (m : Fin n) : Decidable (cyclicStepBetween a b m) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ (_ ∨ _))))

theorem cyclicBetween_self_left {n : ℕ} (a b : Fin (n + 1)) : cyclicBetween a b a := by
  rcases le_or_gt a b with h | h
  · exact Or.inl ⟨h, le_refl a, h⟩
  · exact Or.inr ⟨h, Or.inl (le_refl a)⟩

theorem cyclicBetween_iff_of_le {n : ℕ} {a b : Fin (n + 1)} (k : Fin (n + 1)) (h : a ≤ b) :
    cyclicBetween a b k ↔ a ≤ k ∧ k ≤ b := by
  constructor
  · rintro (⟨_, h₁, h₂⟩ | ⟨h', _⟩)
    · exact ⟨h₁, h₂⟩
    · exact (not_lt_of_ge h h').elim
  · exact fun hk => Or.inl ⟨h, hk⟩

theorem cyclicStepBetween_states {n : ℕ} {a b : Fin (n + 1)} {m : Fin n}
    (h : cyclicStepBetween a b m) : cyclicBetween a b m.castSucc ∧ cyclicBetween a b m.succ := by
  have hs : m.castSucc ≤ m.succ := le_of_lt (Fin.castSucc_lt_succ (i := m))
  rcases h with ⟨hab, ha, hb⟩ | ⟨hba, ha | hb⟩
  · exact ⟨Or.inl ⟨hab, ha, hs.trans hb⟩, Or.inl ⟨hab, ha.trans hs, hb⟩⟩
  · exact ⟨Or.inr ⟨hba, Or.inl ha⟩, Or.inr ⟨hba, Or.inl (ha.trans hs)⟩⟩
  · exact ⟨Or.inr ⟨hba, Or.inr (hs.trans hb)⟩, Or.inr ⟨hba, Or.inr hb⟩⟩

namespace MoveTrace

/-- Untouched squares retain their contents on an ordinary linear interval.
This locality theorem also handles promotion, en passant and castling. -/
theorem board_eq_of_untouched (tr : MoveTrace) (hl : tr.FollowsLegalMoves) (A : Pos)
    {a k : Fin (tr.len + 1)} (hak : a ≤ k)
    (hun : ∀ m : Fin tr.len, a ≤ m.castSucc → m.castSucc < k →
      ¬ (tr.moves m).Touches (tr.before m).turn A) :
    (tr.states k).board A = (tr.states a).board A := by
  revert hak hun
  induction k using Fin.induction with
  | zero => intro hak _; rw [Fin.le_zero_iff.mp hak]
  | succ i ih =>
    intro hak hun
    by_cases he : a = i.succ
    · rw [he]
    · have hai : a ≤ i.castSucc := Fin.le_castSucc_iff.mpr (lt_of_le_of_ne hak he)
      have hu := hun i hai (Fin.castSucc_lt_succ (i := i))
      have hprev := ih hai (fun m h₁ h₂ => hun m h₁ (lt_trans h₂ (Fin.castSucc_lt_succ (i := i))))
      obtain ⟨_, _, hm⟩ := hl i
      change (tr.after i).board A = _
      rw [hm]
      exact (applyBoard_eq_of_not_touches _ _ _ A hu).trans hprev

/-- In a periodic ordinary trace, a square occupied on both sides of a move
cannot have been touched. This rules out identical replacement as well. -/
theorem not_touches_of_occupied_before_after (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (ho : tr.OrdinaryMoves) (i : Fin tr.len) (A : Pos)
    (hb : (tr.before i).board A ≠ none) (ha : (tr.after i).board A ≠ none) :
    ¬ (tr.moves i).Touches (tr.before i).turn A := by
  obtain ⟨src, dst, hm⟩ := ho i
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by simpa only [hm] using hv.movement
  obtain ⟨_, _, _, hne, _⟩ := hv'
  rw [hm, Move.Touches]
  rintro (h | h)
  · subst A
    apply ha
    rw [he, hm]; exact Board.relocate_source _ _ _ _ hne
  · subst A
    exact hb (tr.boardMove_destination_empty_of_periodic hl hp i src dst none hm)

/-- A first touch after an occupied state must move its piece away: an arrival
would capture, contrary to periodic material conservation. No glare premise is
needed to find the departure. -/
theorem departure_of_occupied_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (ho : tr.OrdinaryMoves) (A : Pos) (a : Fin (tr.len + 1))
    (hocc : (tr.states a).board A ≠ none)
    (hex : ∃ m : Fin tr.len, a ≤ m.castSucc ∧ (tr.moves m).Touches (tr.before m).turn A) :
    ∃ (j : Fin tr.len) (dst : Pos), a ≤ j.castSucc ∧ tr.moves j = .boardMove A dst none ∧
      ∀ k : Fin (tr.len + 1), a ≤ k → k ≤ j.castSucc →
        (tr.states k).board A = (tr.states a).board A := by
  classical
  have hP : ∃ n, ∃ h : n < tr.len, a.val ≤ n ∧
      (tr.moves ⟨n, h⟩).Touches (tr.before ⟨n, h⟩).turn A := by
    obtain ⟨m, ha, hm⟩ := hex
    exact ⟨m.val, m.isLt, ha, hm⟩
  obtain ⟨hn, han, htouch⟩ := Nat.find_spec hP
  let j : Fin tr.len := ⟨Nat.find hP, hn⟩
  have haj : a ≤ j.castSucc := han
  have hconst (k : Fin (tr.len + 1)) (hak : a ≤ k) (hkj : k ≤ j.castSucc) :
      (tr.states k).board A = (tr.states a).board A := by
    apply tr.board_eq_of_untouched hl A hak
    intro m ham hmk htm
    have hmj : m.val < Nat.find hP := lt_of_lt_of_le hmk hkj
    exact Nat.find_min hP hmj ⟨m.isLt, ham, htm⟩
  obtain ⟨src, dst, hm⟩ := ho j
  have ht : (tr.moves j).Touches (tr.before j).turn A := htouch
  rw [hm, Move.Touches] at ht
  rcases ht with hA | hA
  · subst src
    exact ⟨j, dst, haj, hm, hconst⟩
  · have hempty := tr.boardMove_destination_empty_of_periodic hl hp j src dst none hm
    have he := hconst j.castSucc haj (le_refl _)
    change (tr.before j).board A = _ at he
    rw [hA, hempty] at he
    apply (hocc ?_).elim
    rw [hA]
    exact he.symm

/-- Proposition 3.3: after arrival of a non-glaring piece, derive its departure
(possibly in the next period) and a same-side sliding witness whose line passes
through the destination. Both pieces retain their contents throughout the
cyclic stay. No move inside that stay touches either square. -/
theorem openable_line_cyclic_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src A : Pos)
    (hm : tr.moves i = .boardMove src A none)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.succ A) :
    ∃ (j : Fin tr.len) (dst B : Pos) (Q : Piece),
      tr.moves j = .boardMove A dst none ∧ Q.owner = (tr.before i).turn ∧
      (Q.kind = .queen ∨ Q.kind = .rook ∨ Q.kind = .bishop) ∧
      Between B (kp 0 Q.owner.opponent) A ∧
      (∀ k : Fin (tr.len + 1), cyclicBetween i.succ j.castSucc k →
        (tr.states k).board A = (tr.states i.succ).board A ∧
        (tr.states k).board B = some Q ∧ tr.GlaresAtEnemyKing kp k B) ∧
      (∀ m : Fin tr.len, cyclicStepBetween i.succ j.castSucc m →
        ¬ (tr.moves m).Touches (tr.before m).turn A ∧
        ¬ (tr.moves m).Touches (tr.before m).turn B) := by
  have hkp := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have ho := tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp
  have hgd := tr.glaringDestinationsCheck_of_periodic_checks kp hl hk hc hp
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src A none) := by simpa only [hm] using hv.movement
  obtain ⟨P, hsrc, hPo, _, _⟩ := hv'
  have hP : (tr.states i.succ).board A = some P := by
    change (tr.after i).board A = some P
    rw [he, hm]; simp [applyMove, applyBoard, hsrc, Piece.promote]
  have hocc : (tr.states i.succ).board A ≠ none := by rw [hP]; exact Option.some_ne_none _
  have howner (j : Fin tr.len) (dst : Pos) (hmj : tr.moves j = .boardMove A dst none)
      (hboard : (tr.states j.castSucc).board A = (tr.states i.succ).board A) :
      (tr.before j).turn = (tr.before i).turn := by
    obtain ⟨_, hj, _⟩ := hl j
    have hj' : PseudoLegal (tr.before j) (.boardMove A dst none) := by simpa only [hmj] using hj.movement
    obtain ⟨p, hp', hpown, _⟩ := hj'
    change (tr.states j.castSucc).board A = some p at hp'
    rw [hboard, hP] at hp'
    have heq : P = p := Option.some.inj hp'
    rw [← heq] at hpown
    exact hpown.symm.trans hPo
  have untouched (j : Fin tr.len) (B : Pos) (Q : Piece)
      (hall : ∀ k, cyclicBetween i.succ j.castSucc k →
        (tr.states k).board A = (tr.states i.succ).board A ∧
        (tr.states k).board B = some Q ∧ tr.GlaresAtEnemyKing kp k B) :
      ∀ m, cyclicStepBetween i.succ j.castSucc m →
        ¬ (tr.moves m).Touches (tr.before m).turn A ∧
        ¬ (tr.moves m).Touches (tr.before m).turn B := by
    intro m hstay
    obtain ⟨hb, ha⟩ := cyclicStepBetween_states hstay
    have hb' := hall m.castSucc hb
    have ha' := hall m.succ ha
    constructor
    · apply tr.not_touches_of_occupied_before_after hl hp ho m A
      · change (tr.states m.castSucc).board A ≠ none; rw [hb'.1]; exact hocc
      · change (tr.states m.succ).board A ≠ none; rw [ha'.1]; exact hocc
    · apply tr.not_touches_of_occupied_before_after hl hp ho m B
      · change (tr.states m.castSucc).board B ≠ none; rw [hb'.2.1]; exact Option.some_ne_none _
      · change (tr.states m.succ).board B ≠ none; rw [ha'.2.1]; exact Option.some_ne_none _
  by_cases hcase : ∃ m : Fin tr.len, i.succ ≤ m.castSucc ∧ (tr.moves m).Touches (tr.before m).turn A
  · obtain ⟨j, dst, hij, hmj, hconst⟩ := tr.departure_of_occupied_of_periodic hl hp ho A i.succ hocc hcase
    have hbj := hconst j.castSucc hij (le_refl _)
    have hngj : ¬ tr.GlaresAtEnemyKing kp j.castSucc A := fun h =>
      hng ((tr.glares_congr kp hl hbj (hkp _ _)).mp h)
    obtain ⟨B, Q, hown, hs, hA, hall, _⟩ := tr.departing_line_witness_of_periodic_checks
      kp hl hk hc hp j A dst hmj hngj (a := i.succ) (fun k h₁ h₂ => by
        rw [hconst k (le_of_lt h₁) h₂]; exact hocc)
    have stay (k : Fin (tr.len + 1)) (hstay : cyclicBetween i.succ j.castSucc k) :
        (tr.states k).board A = (tr.states i.succ).board A ∧
        (tr.states k).board B = some Q ∧ tr.GlaresAtEnemyKing kp k B := by
      obtain ⟨ha, hb⟩ := (cyclicBetween_iff_of_le k hij).mp hstay
      exact ⟨hconst k ha hb, hall k ha hb⟩
    exact ⟨j, dst, B, Q, hmj, hown.trans (howner j dst hmj hbj), hs, hA, stay,
      untouched j B Q stay⟩
  · push Not at hcase
    have hlast : (tr.states (Fin.last tr.len)).board A = (tr.states i.succ).board A :=
      tr.board_eq_of_untouched hl A (Fin.le_last _) (fun m h₁ _ => hcase m h₁)
    have hzero : (tr.states 0).board A = (tr.states i.succ).board A := by rw [← hp.1]; exact hlast
    have hocc0 : (tr.states 0).board A ≠ none := by rw [hzero]; exact hocc
    have hng0 : ¬ tr.GlaresAtEnemyKing kp 0 A := fun h => hng ((tr.glares_congr kp hl hzero (hkp _ _)).mp h)
    have htouch : (tr.moves i).Touches (tr.before i).turn A := by rw [hm]; exact Or.inr rfl
    obtain ⟨j, dst, _, hmj, hconst⟩ := tr.departure_of_occupied_of_periodic hl hp ho A 0 hocc0
      ⟨i, Fin.zero_le _, htouch⟩
    have hji : j.castSucc < i.succ := by
      by_contra hn
      exact hcase j (le_of_not_gt hn) (by rw [hmj]; exact Or.inl rfl)
    have hbj := hconst j.castSucc (Fin.zero_le _) (le_refl _)
    have hngj : ¬ tr.GlaresAtEnemyKing kp j.castSucc A := fun h =>
      hng0 ((tr.glares_congr kp hl hbj (hkp _ _)).mp h)
    obtain ⟨B, Q, hown, hs, hA, hall, _⟩ := tr.departing_line_witness_of_periodic_checks
      kp hl hk hc hp j A dst hmj hngj (a := 0) (fun k h₁ h₂ => by
        rw [hconst k (le_of_lt h₁) h₂]; exact hocc0)
    obtain ⟨hQ0, hg0⟩ := hall 0 (le_refl _) (Fin.zero_le _)
    have hQlast : (tr.states (Fin.last tr.len)).board B = some Q := by rw [hp.1]; exact hQ0
    have hglast : tr.GlaresAtEnemyKing kp (Fin.last tr.len) B :=
      (tr.glares_congr kp hl (hQlast.trans hQ0.symm) (hkp _ _)).mpr hg0
    have hcore := tr.line_witness_persists kp hl ho (fun k => hkp k 0) hgd
      (a := i.succ) (b := Fin.last tr.len) B A Q hQlast hglast hs hA (fun k h₁ _ => by
        rw [tr.board_eq_of_untouched hl A (le_of_lt h₁) (fun m hm₁ _ => hcase m hm₁)]; exact hocc)
    have stay (k : Fin (tr.len + 1)) (hstay : cyclicBetween i.succ j.castSucc k) :
        (tr.states k).board A = (tr.states i.succ).board A ∧
        (tr.states k).board B = some Q ∧ tr.GlaresAtEnemyKing kp k B := by
      rcases hstay with ⟨hle, _, _⟩ | ⟨_, hk' | hk'⟩
      · exact (not_le_of_gt hji hle).elim
      · exact ⟨tr.board_eq_of_untouched hl A hk' (fun m hm₁ _ => hcase m hm₁),
          hcore.1 k hk' (Fin.le_last k)⟩
      · exact ⟨(hconst k (Fin.zero_le _) hk').trans hzero, hall k (Fin.zero_le _) hk'⟩
    exact ⟨j, dst, B, Q, hmj, hown.trans (howner j dst hmj (hbj.trans hzero)), hs, hA, stay,
      untouched j B Q stay⟩

/-- Corollary 3.4: the landing square lies strictly inside a same-side glaring
line to the opponent king and an enemy glaring line to the mover's king.
The enemy checker is obtained from the actual before check, not assumed. -/
theorem openable_destination_lines_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    (∃ B Q, Q.owner = (tr.before i).turn ∧ (tr.after i).board B = some Q ∧
      tr.GlaresAtEnemyKing kp i.succ B ∧ Between B (kp 0 Q.owner.opponent) dst) ∧
    (∃ C X, X.owner = (tr.before i).turn.opponent ∧ (tr.before i).board C = some X ∧
      tr.GlaresAtEnemyKing kp i.castSucc C ∧ Between C (kp 0 X.owner.opponent) dst) := by
  have hkp := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hng' : ¬ tr.GlaresAtEnemyKing kp i.succ dst := fun h =>
    hng (tr.glares_source_of_destination_of_periodic_checks kp hl hk hc hp i src dst hm h)
  obtain ⟨j, _, B, Q, _, ho, _, hB, hall, _⟩ :=
    tr.openable_line_cyclic_of_periodic_checks kp hl hk hc hp i src dst hm hng'
  obtain ⟨_, hQ, hg⟩ := hall i.succ (cyclicBetween_self_left _ _)
  refine ⟨⟨B, Q, ho, hQ, hg, hB⟩, ?_⟩
  obtain ⟨C, X, hX, hXo, _, ha⟩ := tr.exists_slider_checker_of_periodic_checks kp hl hk hc hp
    (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt) i.castSucc
  have hXg : tr.GlaresAtEnemyKing kp i.castSucc C := tr.glares_of_attacks kp i.castSucc C X hX (by
    simpa only [hXo, Color.opponent_opponent] using ha)
  refine ⟨C, X, hXo, hX, hXg, ?_⟩
  have hline := tr.destination_between_checker_of_periodic_checks kp hl hk hc hp i src dst C X hm hX hXo ha
  simpa only [hXo, Color.opponent_opponent, MoveTrace.before] using hline

end MoveTrace
end MPC.Chess
