import MPC.Chess.KingImmobility

/-! With fixed kings and no captures, a board-independent attack cannot be
answered. Thus every actual checker is a queen, rook or bishop. Knights may
still move; this module excludes their checks, not their moves. -/

namespace MPC.Chess.MoveTrace

private theorem checker_is_slider_before (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (q : Pos) (p : Piece)
    (hq : (tr.before i).board q = some p) (ho : p.owner = (tr.before i).turn.opponent)
    (ha : attacks (tr.before i).board p q (kp i.castSucc (tr.before i).turn)) :
    p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop := by
  obtain ⟨src, dst, mover, hm, hs, howner, _, _, _, hd, _⟩ :=
    tr.ordinary_nonKing_nonPawn_move_of_periodic_checks kp hl hk hc hp i
  have hqs : q ≠ src := by
    intro he
    subst q
    have heq := Option.some.inj (hq.symm.trans hs)
    have heo := congrArg Piece.owner heq
    rw [ho, howner] at heo
    exact (tr.before i).turn.opponent_ne heo
  have hqd : q ≠ dst := by
    intro he
    rw [he, hd] at hq
    contradiction
  obtain ⟨_, _, he⟩ := hl i
  rw [hm] at he
  have hqafter : (tr.after i).board q = some p := by
    rw [he]
    change (tr.before i).board.relocate src dst none q = some p
    rwa [Board.relocate_other _ _ _ _ _ hqs hqd]
  have hpos := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp i.succ i.castSucc
  have hsafe := tr.ownKing_safe_after_of_legal kp hl hk i
  have hnot : ¬ attacks (tr.after i).board p q (kp i.castSucc (tr.before i).turn) := by
    intro h
    apply hsafe
    rw [hpos]
    exact ⟨q, p, hqafter, ho, h⟩
  cases hkind : p.kind with
  | queen => exact Or.inl rfl
  | rook => exact Or.inr (Or.inl rfl)
  | bishop => exact Or.inr (Or.inr rfl)
  | king | knight | pawn => exact (hnot (by simpa only [attacks, hkind] using ha)).elim

/-- Classify every checker in every state, including the last state via the
periodic boundary. Positive length is essential for the empty trace. -/
theorem checking_piece_is_slider_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (k : Fin (tr.len + 1))
    (c : Color) (q : Pos) (p : Piece) (hq : (tr.states k).board q = some p)
    (ho : p.owner = c.opponent) (ha : attacks (tr.states k).board p q (kp k c)) :
    p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop := by
  by_cases he : c = (tr.states k).turn
  · subst c
    revert hq ho ha
    refine Fin.lastCases ?_ (fun i hq ho ha => ?_) k
    · intro hq ho ha
      let first : Fin tr.len := ⟨0, hn⟩
      have hpos := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp (Fin.last tr.len) 0
      rw [hp.1] at hq ha
      rw [hp.2] at ho ha
      rw [hpos] at ha
      exact tr.checker_is_slider_before kp hl hk hc hp first q p hq ho ha
    · exact tr.checker_is_slider_before kp hl hk hc hp i q p hq ho ha
  · have he' : c = (tr.states k).turn.opponent := by
      cases c <;> cases ht : (tr.states k).turn <;> simp_all [Color.opponent]
    subst c
    exact (tr.opponent_safe_of_periodic kp hl hk hp hn k ⟨q, p, hq, ho, ha⟩).elim

theorem not_pawn_check_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (k : Fin (tr.len + 1)) (c : Color) (q : Pos)
    (hq : (tr.states k).board q = some ⟨c.opponent, .pawn⟩) :
    ¬ attacks (tr.states k).board ⟨c.opponent, .pawn⟩ q (kp k c) := by
  intro ha
  have h := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp hn k c q _ hq rfl ha
  simp at h

theorem not_knight_check_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (k : Fin (tr.len + 1)) (c : Color) (q : Pos)
    (hq : (tr.states k).board q = some ⟨c.opponent, .knight⟩) :
    ¬ attacks (tr.states k).board ⟨c.opponent, .knight⟩ q (kp k c) := by
  intro ha
  have h := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp hn k c q _ hq rfl ha
  simp at h

/-- The source, owner and actual sliding attack are available for the later
line geometry. No uniqueness of the checker is claimed. -/
theorem exists_slider_checker_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (k : Fin (tr.len + 1)) :
    ∃ q p, (tr.states k).board q = some p ∧ p.owner = (tr.states k).turn.opponent ∧
      (p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop) ∧
      attacks (tr.states k).board p q (kp k (tr.states k).turn) := by
  obtain ⟨q, p, hq, ho, ha⟩ := tr.inCheck_turn_of_periodic_checks kp hl hk hc hp hn k
  exact ⟨q, p, hq, ho,
    tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp hn k _ q p hq ho ha, ha⟩

end MPC.Chess.MoveTrace
