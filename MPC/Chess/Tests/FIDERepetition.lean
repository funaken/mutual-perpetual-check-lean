import MPC.Chess.FIDERepetition

namespace MPC.Chess.Tests

-- Equal positions are the same in the FIDE sense, and a FIDE repetition gives
-- the weaker board-and-turn recurrence used by the main theorem.
example (p : Position) : FIDESamePosition p p := FIDESamePosition.of_eq rfl

example (tr : MoveTrace) (h : tr.states (Fin.last tr.len) = tr.states 0) :
    tr.BoardTurnPeriodic :=
  tr.boardTurnPeriodic_of_fideSamePosition (FIDESamePosition.of_eq h)

-- Board-and-turn recurrence does not require equal castling rights or
-- en-passant targets: two such positions differ as `Position`s.
example : (⟨Board.empty, .white, {}, none⟩ : Position) ≠
    ⟨Board.empty, .white, CastlingRights.ofFunction (fun _ _ => true), some (4, 2)⟩ := by
  intro h
  have := congrArg Position.enPassant h
  simp at this

-- The knight on g1 prevents White from castling even while the right is retained.
private def blockedCastle (turn : Color) (right : Bool) : Position where
  board q :=
    if q = (4, 0) then some ⟨.white, .king⟩
    else if q = (7, 0) then some ⟨.white, .rook⟩
    else if q = (6, 0) then some ⟨.white, .knight⟩
    else if q = (0, 7) then some ⟨.black, .king⟩ else none
  turn := turn
  castlingRights := { whiteKingSide := right }

private theorem castle_blocked (right : Bool) (side : CastleSide) :
    ¬ CastleAllowed (blockedCastle .white right) side := by
  cases right <;> cases side <;> decide

example : KingsWellPlaced (blockedCastle .white true).board
    (fun c => if c = .white then (4, 0) else (0, 7)) := by decide

example (m : Move) :
    (∃ kp, LegalMove (blockedCastle .white true) m kp) ↔
      (∃ kp, LegalMove (blockedCastle .white false) m kp) := by
  have hm : PseudoLegal (blockedCastle .white true) m ↔
      PseudoLegal (blockedCastle .white false) m := by
    cases m with
    | boardMove _ _ _ | enPassant _ _ => rfl
    | castle side => simp [PseudoLegal, castle_blocked]
  constructor
  · rintro ⟨kp, h⟩
    exact ⟨kp, ⟨h.placement, hm.mp h.movement, h.ownKingSafe⟩⟩
  · rintro ⟨kp, h⟩
    exact ⟨kp, ⟨h.placement, hm.mpr h.movement, h.ownKingSafe⟩⟩

-- Loss of White's right distinguishes the positions even on Black's turn.
example (turn : Color) : ¬ FIDESamePosition (blockedCastle turn true) (blockedCastle turn false) :=
  fun h => Bool.noConfusion (congrArg CastlingRights.whiteKingSide h.castlingRights)

-- White can capture e5xd6 en passant unless a black rook on e8 pins the e5 pawn.
private def epPosition (pinned : Bool) (target : Option Pos) : Position where
  board q :=
    if q = (4, 0) then some ⟨.white, .king⟩
    else if q = (0, 7) then some ⟨.black, .king⟩
    else if q = (4, 4) then some ⟨.white, .pawn⟩
    else if q = (3, 4) then some ⟨.black, .pawn⟩
    else if q = (4, 7) ∧ pinned then some ⟨.black, .rook⟩ else none
  turn := .white
  enPassant := target

private def epKings : Color → Pos
  | .white => (4, 0)
  | .black => (0, 7)

example : ¬ FIDESamePosition (epPosition false (some (3, 5))) (epPosition false none) := by
  intro h
  have legal : LegalMove (epPosition false (some (3, 5))) (.enPassant (4, 4) (3, 5)) epKings := by
    decide
  obtain ⟨_, hm⟩ := (h.moves _).mp ⟨epKings, legal⟩
  cases hm.movement.2.2.1

example : PseudoLegal (epPosition true (some (3, 5))) (.enPassant (4, 4) (3, 5)) := by decide

example : FIDESamePosition (epPosition true (some (3, 5))) (epPosition true none) := by
  apply (FIDESamePosition.iff_legal_enPassant
    (p := epPosition true (some (3, 5))) (q := epPosition true none) rfl rfl rfl).mpr
  intro src dst
  constructor
  · rintro ⟨kp, hm⟩
    have onlyPawn : ∀ q, (epPosition true (some (3, 5))).board q = some ⟨.white, .pawn⟩ →
        q = (4, 4) := by decide
    obtain rfl := onlyPawn src hm.movement.1
    obtain rfl := Option.some.inj hm.movement.2.2.1
    have placement : KingsWellPlaced (epPosition true (some (3, 5))).board epKings := by decide
    obtain rfl := placement.positions_unique hm.placement
    exact absurd hm.ownKingSafe (by decide)
  · rintro ⟨_, hm⟩
    cases hm.movement.2.2.1

-- The corollary for FIDE repetitions.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp)
    (hs : FIDESamePosition (tr.states (Fin.last tr.len)) (tr.states 0)) : tr.len = 0 := by
  by_contra h
  exact mutual_perpetual_check_impossible_of_fideSamePosition
    ⟨tr, kp, Nat.pos_of_ne_zero h, hl, hk, hc, hs⟩

end MPC.Chess.Tests
