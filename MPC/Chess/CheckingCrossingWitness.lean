import MPC.Chess.CheckingCrossingSet

/-! Board-square witnesses for Lemma 6.4(1). A check is first blocked at a
crossing. If the checker is not itself a crossing, it stays in place; the
blocker's eventual departure then requires another occupied crossing. -/

namespace MPC.Chess.MoveTrace

/-- An ordinary arrival has a departure with the same piece contents and side somewhere
in the period. The departure may precede the arrival's index (wraparound).
No checking or glare premise is needed for this material/locality result. -/
theorem arrival_piece_departs_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (ho : tr.OrdinaryMoves) (i : Fin tr.len) (src A : Pos)
    (hm : tr.moves i = .boardMove src A none) :
    ∃ (j : Fin tr.len) (dst : Pos), tr.moves j = .boardMove A dst none ∧
      (tr.before j).board A = (tr.after i).board A ∧ (tr.before j).turn = (tr.before i).turn := by
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src A none) := by simpa only [hm] using hv.movement
  obtain ⟨P, hsrc, hPo, _, _⟩ := hv'
  have hP : (tr.states i.succ).board A = some P := by
    change (tr.after i).board A = some P
    rw [he, hm]; simp [applyMove, applyBoard, hsrc, Piece.promote]
  have hocc : (tr.states i.succ).board A ≠ none := by rw [hP]; exact Option.some_ne_none _
  have howner (j : Fin tr.len) (dst : Pos) (hmj : tr.moves j = .boardMove A dst none)
      (hboard : (tr.before j).board A = (tr.after i).board A) :
      (tr.before j).turn = (tr.before i).turn := by
    obtain ⟨_, hj, _⟩ := hl j
    have hj' : PseudoLegal (tr.before j) (.boardMove A dst none) := by simpa only [hmj] using hj.movement
    obtain ⟨p, hp', hpown, _⟩ := hj'
    rw [hboard] at hp'
    change (tr.states i.succ).board A = some p at hp'
    have heq : P = p := Option.some.inj (hP.symm.trans hp')
    rw [← heq] at hpown
    exact hpown.symm.trans hPo
  by_cases hex : ∃ m : Fin tr.len, i.succ ≤ m.castSucc ∧ (tr.moves m).Touches (tr.before m).turn A
  · obtain ⟨j, dst, hij, hmj, hconst⟩ := tr.departure_of_occupied_of_periodic hl hp ho A i.succ hocc hex
    have hbj := hconst j.castSucc hij (le_refl _)
    exact ⟨j, dst, hmj, hbj, howner j dst hmj hbj⟩
  · push Not at hex
    have hlast : (tr.states (Fin.last tr.len)).board A = (tr.states i.succ).board A :=
      tr.board_eq_of_untouched hl A (Fin.le_last _) (fun m h₁ _ => hex m h₁)
    have hzero : (tr.states 0).board A = (tr.states i.succ).board A := by rw [← hp.1]; exact hlast
    have hocc0 : (tr.states 0).board A ≠ none := by rw [hzero]; exact hocc
    have htouch : (tr.moves i).Touches (tr.before i).turn A := by rw [hm]; exact Or.inr rfl
    obtain ⟨j, dst, _, hmj, hconst⟩ := tr.departure_of_occupied_of_periodic hl hp ho A 0 hocc0
      ⟨i, Fin.zero_le _, htouch⟩
    have hbj := (hconst j.castSucc (Fin.zero_le _) (le_refl _)).trans hzero
    exact ⟨j, dst, hmj, hbj, howner j dst hmj hbj⟩

/-- A square outside the finite crossing set is untouched and keeps its
contents, including emptiness. This is derived from the move endpoints. -/
theorem board_eq_of_not_mem_checkingCrossings (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (q : Pos) (hq : q.toPlane ∉ tr.checkingCrossings (kp 0))
    (a b : Fin (tr.len + 1)) : (tr.states a).board q = (tr.states b).board q := by
  have hun (i : Fin tr.len) : ¬ (tr.moves i).Touches (tr.before i).turn q := by
    obtain ⟨src, dst, hm⟩ := tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp i
    obtain ⟨hs, hd⟩ := tr.boardMove_mem_checkingCrossings_of_periodic_checks kp hl hk hc hp i src dst hm
    rw [hm, Move.Touches]
    rintro (rfl | rfl) <;> contradiction
  have hzero (k : Fin (tr.len + 1)) : (tr.states k).board q = (tr.states 0).board q :=
    tr.board_eq_of_untouched hl q (Fin.zero_le k) (fun i _ _ => hun i)
  exact (hzero a).trans (hzero b).symm

theorem mem_checkingCrossings_of_board_ne (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (q : Pos) (a b : Fin (tr.len + 1))
    (hne : (tr.states a).board q ≠ (tr.states b).board q) :
    q.toPlane ∈ tr.checkingCrossings (kp 0) := by
  by_contra hn
  exact hne (tr.board_eq_of_not_mem_checkingCrossings kp hl hk hc hp q hn a b)

private theorem slider_path {b : Board} {p : Piece} {a k : Pos}
    (hs : p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop)
    (ha : attacks b p a k) : pathClear b a k := by
  rcases hs with hs | hs | hs <;> simp only [attacks, hs] at ha <;> exact ha.2.2

private theorem checker_two_crossings_before (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (C : Pos) (X : Piece)
    (hX : (tr.before i).board C = some X) (ho : X.owner = (tr.before i).turn.opponent)
    (ha : attacks (tr.before i).board X C (kp i.castSucc (tr.before i).turn)) :
    ∃ A B : Pos, A ≠ B ∧ A.toPlane ∈ tr.checkingCrossings (kp 0) ∧
      B.toPlane ∈ tr.checkingCrossings (kp 0) ∧
      Between C (kp 0 (tr.before i).turn) A ∧
      (B = C ∨ Between C (kp 0 (tr.before i).turn) B) := by
  have hkp := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hlen : 0 < tr.len := Nat.zero_lt_of_lt i.isLt
  have hs := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp hlen
    i.castSucc (tr.before i).turn C X hX ho ha
  obtain ⟨src, A, hm⟩ := tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp i
  have hA := tr.destination_between_checker_of_periodic_checks kp hl hk hc hp i src A C X hm hX ho ha
  have hAmem := (tr.boardMove_mem_checkingCrossings_of_periodic_checks kp hl hk hc hp i src A hm).2
  by_cases hC : C.toPlane ∈ tr.checkingCrossings (kp 0)
  · exact ⟨A, C, hA.1, hAmem, hC, hA, Or.inl rfl⟩
  · obtain ⟨j, dst, hmj, _, hturn⟩ := tr.arrival_piece_departs_of_periodic hl hp
      (tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp) i src A hm
    have hXj : (tr.after j).board C = some X :=
      (tr.board_eq_of_not_mem_checkingCrossings kp hl hk hc hp C hC j.succ i.castSucc).trans hX
    rw [hkp i.castSucc 0] at ha
    have hnot : ¬ pathClear (tr.after j).board C (kp 0 (tr.before i).turn) := by
      intro hpath
      apply tr.ownKing_safe_after_of_legal kp hl hk j
      rw [hkp j.succ 0, hturn]
      exact ⟨C, X, hXj, ho, attacks_of_pathClear _ _ X C _ ha hpath⟩
    unfold pathClear at hnot
    push Not at hnot
    obtain ⟨B, hB, hocc⟩ := hnot
    obtain ⟨_, hvj, hej⟩ := hl j
    have hvj' : PseudoLegal (tr.before j) (.boardMove A dst none) := by simpa only [hmj] using hvj.movement
    obtain ⟨_, _, _, hne, _⟩ := hvj'
    have hAempty : (tr.after j).board A = none := by
      rw [hej, hmj]; exact Board.relocate_source _ _ _ _ hne
    have hAB : A ≠ B := by intro he; subst B; exact hocc hAempty
    have hBempty : (tr.before i).board B = none := slider_path hs ha B hB
    have hBmem := tr.mem_checkingCrossings_of_board_ne kp hl hk hc hp B j.succ i.castSucc
      (by change (tr.after j).board B ≠ (tr.before i).board B; rwa [hBempty])
    exact ⟨A, B, hAB, hAmem, hBmem, hA, Or.inr hB⟩

/-- Two distinct board crossings lie no farther from the king than any actual
checker; at least one lies strictly between the checker and king. The final state uses the
reply at state zero. Neither immobility nor two-crossing existence is assumed. -/
theorem checker_two_crossings_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (k : Fin (tr.len + 1))
    (c : Color) (C : Pos) (X : Piece) (hX : (tr.states k).board C = some X)
    (ho : X.owner = c.opponent) (ha : attacks (tr.states k).board X C (kp k c)) :
    ∃ A B : Pos, A ≠ B ∧ A.toPlane ∈ tr.checkingCrossings (kp 0) ∧
      B.toPlane ∈ tr.checkingCrossings (kp 0) ∧ Between C (kp 0 c) A ∧
      (B = C ∨ Between C (kp 0 c) B) := by
  by_cases he : c = (tr.states k).turn
  · subst c
    revert hX ho ha
    refine Fin.lastCases ?_ (fun i hX ho ha => ?_) k
    · intro hX ho ha
      let first : Fin tr.len := ⟨0, hn⟩
      have hpos := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp (Fin.last tr.len) 0
      rw [hp.1] at hX ha
      rw [hp.2] at ho ha ⊢
      rw [hpos] at ha
      exact tr.checker_two_crossings_before kp hl hk hc hp first C X hX ho ha
    · exact tr.checker_two_crossings_before kp hl hk hc hp i C X hX ho ha
  · have he' : c = (tr.states k).turn.opponent := by
      cases c <;> cases ht : (tr.states k).turn <;> simp_all [Color.opponent]
    subst c
    exact (tr.opponent_safe_of_periodic kp hl hk hp hn k ⟨C, X, hX, ho, ha⟩).elim

/-- The board witnesses belong to the given checking ray. They are geometric
points for the later rational-order argument, not yet the selected A₁/A₂. -/
theorem checkingRay_two_crossings_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) :
    ∃ A B : Pos, A ≠ B ∧ A.toPlane ∈ tr.checkingCrossings (kp 0) ∧
      B.toPlane ∈ tr.checkingCrossings (kp 0) ∧ OnRay (kp 0 c) d A ∧ OnRay (kp 0 c) d B := by
  obtain ⟨k, C, X, hX, ho, ha, hdir⟩ := hr
  have ha' : attacks (tr.states k).board X C (kp k c) := by
    rw [tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp k 0]; exact ha
  obtain ⟨A, B, hne, hA, hB, hbetween, hlast⟩ :=
    tr.checker_two_crossings_of_periodic_checks kp hl hk hc hp hn k c C X hX ho ha'
  refine ⟨A, B, hne, hA, hB, hdir.of_between hbetween, ?_⟩
  rcases hlast with rfl | hlast
  · exact hdir
  · exact hdir.of_between hlast

end MPC.Chess.MoveTrace
