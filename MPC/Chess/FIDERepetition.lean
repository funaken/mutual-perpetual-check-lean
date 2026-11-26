import MPC.Chess.Impossibility

/-! The main theorem in terms of FIDE Laws of Chess, Article 9.2. A repeated
position in the FIDE sense has the same side to move and the same pieces on the
same squares, so it recurs in board and side to move. The repetition rules
themselves (claims, threefold or fivefold repetition) are not used as grounds
for the impossibility. -/

namespace MPC.Chess

/-- The model's repetition relation for FIDE Article 9.2.3. Both players' retained
castling rights count even when castling is temporarily blocked (9.2.3.2).
`moves` compares legal moves for the side to move, including any legal en-passant
capture (9.2.3.1). -/
structure FIDESamePosition (p q : Position) : Prop where
  turn : p.turn = q.turn
  board : p.board = q.board
  castlingRights : p.castlingRights = q.castlingRights
  moves : ∀ m, (∃ kp, LegalMove p m kp) ↔ (∃ kp, LegalMove q m kp)

theorem FIDESamePosition.of_eq {p q : Position} (h : p = q) : FIDESamePosition p q :=
  h ▸ ⟨rfl, rfl, rfl, fun _ => Iff.rfl⟩

/-- With the same board, turn and castling rights, only legal en-passant captures
can distinguish two positions for repetition. -/
theorem FIDESamePosition.iff_legal_enPassant {p q : Position}
    (hb : p.board = q.board) (ht : p.turn = q.turn) (hr : p.castlingRights = q.castlingRights) :
    FIDESamePosition p q ↔ ∀ src dst,
      (∃ kp, LegalMove p (.enPassant src dst) kp) ↔ (∃ kp, LegalMove q (.enPassant src dst) kp) := by
  constructor
  · exact fun h src dst => h.moves (.enPassant src dst)
  · intro hep
    refine ⟨ht, hb, hr, ?_⟩
    cases p
    cases q
    cases hb
    cases ht
    cases hr
    intro move
    cases move with
    | enPassant src dst => exact hep src dst
    | boardMove _ _ _ | castle _ =>
      constructor <;> rintro ⟨kp, h⟩ <;> exact ⟨kp, ⟨h.placement, h.movement, h.ownKingSafe⟩⟩

/-- A FIDE repetition of the initial position recurs in board and side to move. -/
theorem MoveTrace.boardTurnPeriodic_of_fideSamePosition (tr : MoveTrace)
    (h : FIDESamePosition (tr.states (Fin.last tr.len)) (tr.states 0)) :
    tr.BoardTurnPeriodic :=
  ⟨h.board, h.turn⟩

/-- Corollary: no positive-length legal sequence that checks the opponent with
every move returns to the same position in the sense of FIDE Article 9.2. -/
theorem mutual_perpetual_check_impossible_of_fideSamePosition :
    ¬ ∃ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos),
      0 < tr.len ∧ tr.FollowsLegalMoves ∧ tr.KingsWellPlaced kp ∧
        tr.EveryMoveChecksOpponent kp ∧
          FIDESamePosition (tr.states (Fin.last tr.len)) (tr.states 0) := by
  rintro ⟨tr, kp, hn, hl, hk, hc, hs⟩
  exact mutual_perpetual_check_impossible
    ⟨tr, kp, hn, hl, hk, hc, tr.boardTurnPeriodic_of_fideSamePosition hs⟩

end MPC.Chess
