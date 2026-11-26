import MPC.Chess.PeriodicReduction

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

private def baseBoard : Board := fun q =>
  if q = kingHome .white then some ⟨.white, .king⟩
  else if q = kingHome .black then some ⟨.black, .king⟩ else none

private def putPiece (b : Board) (q : Pos) (p : Piece) : Board :=
  fun r => if r = q then some p else b r

private def capturePosition (c : Color) : Position :=
  ⟨putPiece (putPiece baseBoard (0, c.homeRank) ⟨c, .rook⟩)
    (0, c.opponent.homeRank) ⟨c.opponent, .bishop⟩, c, {}, none⟩

example (c : Color) :
    let pos := capturePosition c
    let mv := Move.boardMove (0, c.homeRank) (0, c.opponent.homeRank) none
    PseudoLegal pos mv ∧ pos.board.pieceCount = 4 ∧
      (applyMove pos mv).board.pieceCount = 3 := by
  cases c <;> decide

private def pawnPushPosition (c : Color) : Position :=
  ⟨putPiece baseBoard (3, c.pawnRank) ⟨c, .pawn⟩, c, {}, none⟩

example (c : Color) :
    let pos := pawnPushPosition c
    let one := Move.boardMove (3, c.pawnRank) (3, c.doubleStepTargetRank) none
    let two := Move.boardMove (3, c.pawnRank) (3, c.opponent.enPassantRank) none
    PseudoLegal pos one ∧ PseudoLegal pos two ∧
      pos.board.pawnProgress = 1 ∧ (applyMove pos one).board.pawnProgress = 2 ∧
      (applyMove pos two).board.pawnProgress = 3 ∧
      (applyMove pos two).board.pieceCount = 3 ∧ (applyMove pos two).board.pawnCount = 1 := by
  cases c <;> decide

example (c : Color) :
    let pos : Position := { (pawnPushPosition c) with board :=
      (putPiece (pawnPushPosition c).board (2, c.doubleStepTargetRank) ⟨c.opponent, .pawn⟩) }
    let mv := Move.boardMove (3, c.pawnRank) (2, c.doubleStepTargetRank) none
    PseudoLegal pos mv ∧ pos.board.pieceCount = 4 ∧ (applyMove pos mv).board.pieceCount = 3 ∧
      pos.board.pawnCount = 2 ∧ (applyMove pos mv).board.pawnCount = 1 := by
  cases c <;> decide

private def promotionPosition (c : Color) : Position :=
  ⟨putPiece baseBoard (0, c.opponent.pawnRank) ⟨c, .pawn⟩, c, {}, none⟩

-- Promotion preserves occupancy on a quiet move but removes a pawn. Its
-- progress drops, so progress monotonicity must be proved after excluding it.
example (c : Color) (q : Promotion) :
    let pos := promotionPosition c
    let mv := Move.boardMove (0, c.opponent.pawnRank) (0, c.promotionRank) (some q)
    PseudoLegal pos mv ∧ pos.board.pieceCount = 3 ∧ (applyMove pos mv).board.pieceCount = 3 ∧
      pos.board.pawnCount = 1 ∧ (applyMove pos mv).board.pawnCount = 0 ∧
      pos.board.pawnProgress = 6 ∧ (applyMove pos mv).board.pawnProgress = 0 := by
  cases c <;> cases q <;> decide

example (c : Color) (q : Promotion) :
    let pos : Position := { (promotionPosition c) with board :=
      (putPiece (promotionPosition c).board (1, c.promotionRank) ⟨c.opponent, .rook⟩) }
    let mv := Move.boardMove (0, c.opponent.pawnRank) (1, c.promotionRank) (some q)
    PseudoLegal pos mv ∧ pos.board.pieceCount = 4 ∧ (applyMove pos mv).board.pieceCount = 3 ∧
      pos.board.pawnCount = 1 ∧ (applyMove pos mv).board.pawnCount = 0 := by
  cases c <;> cases q <;> decide

private def epPosition (c : Color) : Position :=
  ⟨putPiece (putPiece baseBoard (3, c.enPassantRank) ⟨c, .pawn⟩)
    (4, c.enPassantRank) ⟨c.opponent, .pawn⟩,
    c, {}, some (4, c.opponent.doubleStepTargetRank)⟩

example (c : Color) :
    let pos := epPosition c
    let mv := Move.enPassant (3, c.enPassantRank) (4, c.opponent.doubleStepTargetRank)
    PseudoLegal pos mv ∧ pos.board.pieceCount = 4 ∧ (applyMove pos mv).board.pieceCount = 3 ∧
      pos.board.pawnCount = 2 ∧ (applyMove pos mv).board.pawnCount = 1 ∧
      pos.board.pawnProgress = 7 ∧ (applyMove pos mv).board.pawnProgress = 5 := by
  cases c <;> decide

private def castlePosition (c : Color) (side : CastleSide) : Position :=
  ⟨putPiece baseBoard (rookHome c side) ⟨c, .rook⟩, c,
    CastlingRights.ofFunction (fun _ _ => true), none⟩

example (c : Color) (side : CastleSide) :
    let pos := castlePosition c side
    PseudoLegal pos (.castle side) ∧ pos.board.pieceCount = 3 ∧
      (applyMove pos (.castle side)).board.pieceCount = 3 ∧
      (applyMove pos (.castle side)).board.pawnCount = 0 ∧
      (applyMove pos (.castle side)).board.pawnProgress = 0 := by
  cases c <;> cases side <;> decide

-- An empty trace has no moves to exclude. Its actual kings need not be checked.
example (c : Color) :
    let tr := MoveTrace.empty ⟨baseBoard, c, {}, none⟩
    tr.FollowsLegalMoves ∧ tr.BoardTurnPeriodic ∧
      tr.KingsWellPlaced (fun _ => kingHome) ∧ tr.EveryMoveChecksOpponent (fun _ => kingHome) ∧
      ¬ inCheck (tr.states 0).board (tr.states 0).turn (kingHome (tr.states 0).turn) := by
  refine ⟨fun i => Fin.elim0 i, ⟨rfl, rfl⟩, ?_, fun i => Fin.elim0 i, ?_⟩
  · intro _
    change KingsWellPlaced baseBoard kingHome
    decide
  · cases c <;> decide

example (initial : Position) (i j : Fin 1) :
    ((MoveTrace.empty initial).states i).board.pieceCount =
      ((MoveTrace.empty initial).states j).board.pieceCount := by
  exact (MoveTrace.empty initial).pieceCount_eq_of_periodic
    (fun k => Fin.elim0 k) ⟨rfl, rfl⟩ i j

-- A legal eight-ply cycle starts by castling, then returns the king and rook.
-- The other king shuttles on its home rank. Both starting colors are covered.
private def cycleStart (c : Color) : Position :=
  { (castlePosition c .kingSide) with
    castlingRights := CastlingRights.ofFunction (fun o s => decide (o = c ∧ s = .kingSide)) }

private def cycleMove (c : Color) : ℕ → Move
  | 0 => .castle .kingSide
  | 1 => .boardMove (kingHome c.opponent) (3, c.opponent.homeRank) none
  | 2 => .boardMove (6, c.homeRank) (5, c.pawnRank) none
  | 3 => .boardMove (3, c.opponent.homeRank) (kingHome c.opponent) none
  | 4 => .boardMove (5, c.homeRank) (7, c.homeRank) none
  | 5 => .boardMove (kingHome c.opponent) (3, c.opponent.homeRank) none
  | 6 => .boardMove (5, c.pawnRank) (kingHome c) none
  | _ => .boardMove (3, c.opponent.homeRank) (kingHome c.opponent) none

private def cycleState (c : Color) : ℕ → Position
  | 0 => cycleStart c
  | n + 1 => applyMove (cycleState c n) (cycleMove c n)

private def cycleKingPos (c : Color) (n : ℕ) (o : Color) : Pos :=
  if o = c then
    if n = 0 ∨ n = 7 ∨ n = 8 then kingHome c
    else if n = 1 ∨ n = 2 then (6, c.homeRank) else (5, c.pawnRank)
  else if n = 2 ∨ n = 3 ∨ n = 6 ∨ n = 7 then (3, c.opponent.homeRank)
  else kingHome c.opponent

private def cycleTrace (c : Color) : MoveTrace where
  len := 8
  states := fun i => cycleState c i.val
  moves := fun i => cycleMove c i.val

private theorem cycle_moves_legal (c : Color) :
    ∀ i : Fin 8, LegalMove (cycleState c i.val) (cycleMove c i.val) (cycleKingPos c i.val) := by
  cases c <;> decide

private theorem cycle_legal (c : Color) : (cycleTrace c).FollowsLegalMoves := by
  intro i
  exact ⟨cycleKingPos c i.val, cycle_moves_legal c i, rfl⟩

private theorem cycle_periodic (c : Color) : (cycleTrace c).BoardTurnPeriodic := by
  constructor
  · funext q
    have h : ∀ r, (cycleState c 8).board r = (cycleStart c).board r := by cases c <;> decide
    exact h q
  · cases c <;> rfl

example (c : Color) :
    (cycleTrace c).KingsWellPlaced (fun i => cycleKingPos c i.val) := by
  change ∀ i : Fin 9, KingsWellPlaced (cycleState c i.val).board (cycleKingPos c i.val)
  cases c <;> decide

example (c : Color) :
    (cycleTrace c).FollowsLegalMoves ∧ (cycleTrace c).BoardTurnPeriodic ∧
    (cycleTrace c).moves (0 : Fin 8) = .castle .kingSide ∧
    ((cycleTrace c).states (8 : Fin 9)).castlingRights ≠
      ((cycleTrace c).states (0 : Fin 9)).castlingRights := by
  refine ⟨cycle_legal c, cycle_periodic c, rfl, ?_⟩
  cases c <;> decide

example (c : Color) :
    ¬ (cycleTrace c).EveryMoveChecksOpponent (fun i => cycleKingPos c i.val) := by
  intro h
  have h0 := h (0 : Fin 8)
  have hn : ¬ inCheck (cycleState c 1).board c.opponent (cycleKingPos c 1 c.opponent) := by
    cases c <;> decide
  exact hn h0

-- All indices, including reversed pairs and endpoints, use the new invariants.
example (c : Color) (i j : Fin 9) :
    ((cycleTrace c).states i).board.pieceCount = ((cycleTrace c).states j).board.pieceCount ∧
    ((cycleTrace c).states i).board.pawnCount = ((cycleTrace c).states j).board.pawnCount ∧
    ((cycleTrace c).states i).board.pawnProgress = ((cycleTrace c).states j).board.pawnProgress := by
  exact ⟨(cycleTrace c).pieceCount_eq_of_periodic (cycle_legal c) (cycle_periodic c) i j,
    (cycleTrace c).pawnCount_eq_of_periodic (cycle_legal c) (cycle_periodic c) i j,
    (cycleTrace c).pawnProgress_eq_of_periodic (cycle_legal c) (cycle_periodic c) i j⟩

-- A checking prefix need not start in check: the cyclic boundary is essential.
private def checkStart (c : Color) : Position :=
  ⟨putPiece baseBoard (0, c.homeRank) ⟨c, .rook⟩, c, {}, none⟩

private def checkMove (c : Color) : Move :=
  .boardMove (0, c.homeRank) (0, c.opponent.homeRank) none

private def checkTrace (c : Color) : MoveTrace :=
  .single (checkStart c) (applyMove (checkStart c) (checkMove c)) (checkMove c)

example (c : Color) :
    (checkTrace c).FollowsLegalMoves ∧
    (checkTrace c).EveryMoveChecksOpponent (fun _ => kingHome) ∧
    ¬ (checkTrace c).BoardTurnPeriodic ∧ ¬ inCheck (checkStart c).board c (kingHome c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (MoveTrace.single_follows_iff _ _ _ LegalTransition).mpr
    refine ⟨kingHome, ?_, rfl⟩
    cases c <;> decide
  · intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    cases c <;> decide
  · intro hp
    exact c.opponent_ne hp.2
  · cases c <;> decide

end MPC.Chess.Tests
