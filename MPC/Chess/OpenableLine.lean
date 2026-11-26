import MPC.Chess.PeriodicGlare

/-! Occupied intervals on a glaring line. Local persistence separates the
ordinary-move, fixed-king and checking-destination premises. Periodic legal
mutual checks supply them; immobility of the witness is a conclusion. -/

namespace MPC.Chess

/-- Removing the source can only unblock a path; adding the destination can
block it only if that square is inside the path. -/
theorem attacks_relocate_of_not_between (b : Board) (p : Piece) (a t src dst : Pos)
    (choice : Option Promotion) (ha : attacks b p a t) (hd : ¬ Between a t dst) :
    attacks (b.relocate src dst choice) p a t := by
  have path (hc : pathClear b a t) : pathClear (b.relocate src dst choice) a t := by
    intro q hq
    have hqd : q ≠ dst := fun he => hd (he ▸ hq)
    simp [Board.relocate, hqd, hc q hq]
  cases hk : p.kind with
  | king | knight | pawn => simpa only [attacks, hk] using ha
  | queen | rook | bishop =>
    simp only [attacks, hk] at ha ⊢
    exact ⟨ha.1, ha.2.1, path ha.2.2⟩

namespace MoveTrace

/-- A local interface for unpromoted ordinary moves, derived in the periodic
application. This is not a field of the trace. -/
def OrdinaryMoves (tr : MoveTrace) : Prop :=
  ∀ i, ∃ src dst, tr.moves i = .boardMove src dst none

/-- The local property supplied by Lemmas 2.5–2.8. -/
def GlaringDestinationsCheck (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos) : Prop :=
  ∀ i src dst, tr.moves i = .boardMove src dst none →
    tr.GlaresAtEnemyKing kp i.succ dst →
      hasDestinationChecker (tr.after i).board dst (tr.before i).turn.opponent
        (kp i.succ (tr.before i).turn.opponent)

theorem ordinaryMoves_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) : tr.OrdinaryMoves := by
  intro i
  obtain ⟨src, dst, _, hm, _⟩ := tr.ordinary_nonKing_nonPawn_move_of_periodic_checks kp hl hk hc hp i
  exact ⟨src, dst, hm⟩

theorem glaringDestinationsCheck_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) : tr.GlaringDestinationsCheck kp := by
  intro i src dst hm hg
  exact tr.destinationChecker_of_source_glares kp hl hk hc hp i src dst hm
    (tr.glares_source_of_destination_of_periodic_checks kp hl hk hc hp i src dst hm hg)

private theorem before_of_glaring_through_occupied (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (ho : tr.OrdinaryMoves) (hkp : ∀ k, kp k = kp 0)
    (hgd : tr.GlaringDestinationsCheck kp) (i : Fin tr.len) (B A : Pos) (Q : Piece)
    (hQ : (tr.states i.succ).board B = some Q) (hg : tr.GlaresAtEnemyKing kp i.succ B)
    (hs : Q.kind = .queen ∨ Q.kind = .rook ∨ Q.kind = .bishop)
    (hA : Between B (kp 0 Q.owner.opponent) A)
    (hocc : (tr.states i.succ).board A ≠ none) :
    (tr.states i.castSucc).board B = some Q ∧ ¬ (tr.moves i).Touches (tr.before i).turn B := by
  obtain ⟨src, dst, hm⟩ := ho i
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by simpa only [hm] using hv.movement
  obtain ⟨_, _, _, hne, _⟩ := hv'
  have hd : B ≠ dst := by
    intro hd
    have hg' : tr.GlaresAtEnemyKing kp i.succ dst := hd ▸ hg
    obtain ⟨p, hpres, hown, ha⟩ := hgd i src dst hm hg'
    rw [← hd] at hpres ha
    have heq : p = Q := Option.some.inj (hpres.symm.trans hQ)
    subst p
    have htarget : (tr.before i).turn.opponent = Q.owner.opponent := by simp [hown]
    rw [hkp, htarget] at ha
    have hclear : pathClear (tr.after i).board B (kp 0 Q.owner.opponent) := by
      rcases hs with hs | hs | hs <;> simp only [attacks, hs] at ha <;> exact ha.2.2
    exact hocc (hclear A hA)
  have hsrc : B ≠ src := by
    intro hB; subst B
    have hempty : (tr.states i.succ).board src = none := by
      change (tr.after i).board src = none
      rw [he, hm]; exact Board.relocate_source _ _ _ _ hne
    rw [hQ] at hempty
    contradiction
  refine ⟨?_, ?_⟩
  · have hb : (tr.states i.succ).board B = (tr.states i.castSucc).board B := by
      change (tr.after i).board B = (tr.before i).board B
      rw [he, hm]; exact Board.relocate_other _ _ _ _ _ hsrc hd
    exact hb.symm.trans hQ
  · simpa only [hm, Move.Touches, not_or] using And.intro hsrc hd

/-- Backwards persistence over an occupied interval. The witness keeps its
contents and glare at every state, and no intervening move touches its square.
This local theorem does not assume periodicity. -/
theorem line_witness_persists (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (ho : tr.OrdinaryMoves) (hkp : ∀ k, kp k = kp 0)
    (hgd : tr.GlaringDestinationsCheck kp) {a b : Fin (tr.len + 1)} (B A : Pos) (Q : Piece)
    (hQ : (tr.states b).board B = some Q) (hg : tr.GlaresAtEnemyKing kp b B)
    (hs : Q.kind = .queen ∨ Q.kind = .rook ∨ Q.kind = .bishop)
    (hA : Between B (kp 0 Q.owner.opponent) A)
    (hocc : ∀ k : Fin (tr.len + 1), a < k → k ≤ b → (tr.states k).board A ≠ none) :
    (∀ k : Fin (tr.len + 1), a ≤ k → k ≤ b →
      (tr.states k).board B = some Q ∧ tr.GlaresAtEnemyKing kp k B) ∧
    (∀ m : Fin tr.len, a ≤ m.castSucc → m.succ ≤ b →
      ¬ (tr.moves m).Touches (tr.before m).turn B) := by
  have key : ∀ n : ℕ, ∀ k : Fin (tr.len + 1), k.val + n = b.val → a ≤ k →
      (tr.states k).board B = some Q := by
    intro n
    induction n with
    | zero =>
      intro k he _
      rw [show k = b from Fin.ext (by omega)]
      exact hQ
    | succ n ih =>
      intro k he hak
      have hkl : k.val < tr.len := by have := b.isLt; omega
      let i : Fin tr.len := ⟨k.val, hkl⟩
      have hki : k = i.castSucc := Fin.ext rfl
      have hai : a < i.succ := by change a.val < k.val + 1; exact Nat.lt_succ_of_le hak
      have hib : i.succ ≤ b := by change k.val + 1 ≤ b.val; omega
      have hqi := ih i.succ (by change k.val + 1 + n = b.val; omega) (le_of_lt hai)
      have hgi : tr.GlaresAtEnemyKing kp i.succ B :=
        (tr.glares_congr kp hl (hqi.trans hQ.symm) ((hkp _).trans (hkp _).symm)).mpr hg
      rw [hki]
      exact (tr.before_of_glaring_through_occupied kp hl ho hkp hgd i B A Q hqi hgi hs hA
        (hocc i.succ hai hib)).1
  have hall (k : Fin (tr.len + 1)) (hak : a ≤ k) (hkb : k ≤ b) :
      (tr.states k).board B = some Q ∧ tr.GlaresAtEnemyKing kp k B := by
    have hqk := key (b.val - k.val) k (by change k.val ≤ b.val at hkb; omega) hak
    exact ⟨hqk, (tr.glares_congr kp hl (hqk.trans hQ.symm) ((hkp _).trans (hkp _).symm)).mpr hg⟩
  refine ⟨hall, ?_⟩
  intro m ham hmb
  have has : a < m.succ := lt_of_le_of_lt ham (Fin.castSucc_lt_succ (i := m))
  obtain ⟨hqm, hgm⟩ := hall m.succ (le_of_lt has) hmb
  exact (tr.before_of_glaring_through_occupied kp hl ho hkp hgd m B A Q hqm hgm hs hA
    (hocc m.succ has hmb)).2

/-- A non-glaring departure supplies a same-side slider witness, already present
and glaring throughout the preceding occupied interval. -/
theorem departing_line_witness_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (j : Fin tr.len) (A dst : Pos)
    (hm : tr.moves j = .boardMove A dst none)
    (hng : ¬ tr.GlaresAtEnemyKing kp j.castSucc A) {a : Fin (tr.len + 1)}
    (hocc : ∀ k : Fin (tr.len + 1), a < k → k ≤ j.castSucc → (tr.states k).board A ≠ none) :
    ∃ B Q, Q.owner = (tr.before j).turn ∧
      (Q.kind = .queen ∨ Q.kind = .rook ∨ Q.kind = .bishop) ∧
      Between B (kp 0 Q.owner.opponent) A ∧
      (∀ k : Fin (tr.len + 1), a ≤ k → k ≤ j.castSucc →
        (tr.states k).board B = some Q ∧ tr.GlaresAtEnemyKing kp k B) ∧
      (∀ m : Fin tr.len, a ≤ m.castSucc → m.succ ≤ j.castSucc →
        ¬ (tr.moves m).Touches (tr.before m).turn B) := by
  have hconst := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hu := (tr.unblockedChecker_iff_not_source_glares_of_periodic_checks kp hl hk hc hp
    j A dst hm).mpr hng
  obtain ⟨B, Q, _, _, hQ0, hQ1, hown, _, ha, hA, _⟩ := hu
  have ho : Q.owner = (tr.before j).turn := by simpa using hown
  have hs := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp
    (lt_of_le_of_lt (Nat.zero_le j.val) j.isLt) j.succ (tr.before j).turn.opponent B Q hQ1 hown ha
  rw [hconst j.succ 0, ← ho] at ha hA
  have hg1 : tr.GlaresAtEnemyKing kp j.succ B :=
    tr.glares_of_attacks kp j.succ B Q hQ1 (by rw [hconst j.succ 0]; exact ha)
  have hg0 := (tr.glares_congr kp hl (hQ0.trans hQ1.symm) (hconst _ _)).mpr hg1
  exact ⟨B, Q, ho, hs, hA,
    tr.line_witness_persists kp hl (tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp)
      (fun k => hconst k 0) (tr.glaringDestinationsCheck_of_periodic_checks kp hl hk hc hp)
      B A Q hQ0 hg0 hs hA hocc⟩

/-- An enemy checker must be blocked at the destination. Capturing the checker
has already been excluded by periodicity, so the destination is strictly inside
its line (stronger than the endpoint allowance in the paper's Corollary 3.4). -/
theorem destination_between_checker_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst C : Pos) (X : Piece)
    (hm : tr.moves i = .boardMove src dst none)
    (hX : (tr.before i).board C = some X) (ho : X.owner = (tr.before i).turn.opponent)
    (ha : attacks (tr.before i).board X C (kp i.castSucc (tr.before i).turn)) :
    Between C (kp 0 (tr.before i).turn) dst := by
  have hconst := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by simpa only [hm] using hv.movement
  obtain ⟨p, hs, hpown, _, _⟩ := hv'
  have hCs : C ≠ src := by
    intro hC; subst C
    have hqp : X = p := Option.some.inj (hX.symm.trans hs)
    rw [hqp, hpown] at ho
    exact (tr.before i).turn.opponent_ne ho.symm
  have hCd : C ≠ dst := by
    intro hC; subst C
    rw [tr.boardMove_destination_empty_of_periodic hl hp i src dst none hm] at hX
    contradiction
  by_contra hnot
  apply tr.ownKing_safe_after_of_legal kp hl hk i
  refine ⟨C, X, ?_, ho, ?_⟩
  · rw [he, hm]; exact (Board.relocate_other _ _ _ _ _ hCs hCd).trans hX
  · rw [hconst i.succ 0]
    rw [hconst i.castSucc 0] at ha
    rw [he, hm]
    exact attacks_relocate_of_not_between _ X C _ src dst none ha hnot

end MoveTrace
end MPC.Chess
