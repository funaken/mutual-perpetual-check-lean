import MPC.Chess.LegalMove

namespace MPC.Chess.Tests

set_option maxRecDepth 16384
set_option maxHeartbeats 800000

private def kings : Board := fun q =>
  if q = kingHome .white then some ⟨.white, .king⟩
  else if q = kingHome .black then some ⟨.black, .king⟩ else none

private def put (b : Board) (q : Pos) (p : Piece) : Board :=
  fun r => if r = q then some p else b r

private def allRights : CastlingRights := ⟨true, true, true, true⟩

private def pawnStart (c : Color) : Pos := (3, c.pawnRank)

private def pawnSingle (c : Color) : Pos := (3, c.doubleStepTargetRank)

private def pawnDouble (c : Color) : Pos := (3, c.opponent.enPassantRank)

private def pawnPosition (c : Color) : Position :=
  ⟨put kings (pawnStart c) ⟨c, .pawn⟩, c, {}, none⟩

example (c : Color) :
    LegalMove (pawnPosition c) (.boardMove (pawnStart c) (pawnSingle c) none) kingHome ∧
    LegalMove (pawnPosition c) (.boardMove (pawnStart c) (pawnDouble c) none) kingHome := by
  cases c <;> decide

-- A blocked double push, a backward push, and a double push off the starting
-- rank are rejected. The diagonal destination must contain an enemy piece.
example :
    ¬ PseudoLegal { (pawnPosition .white) with
        board := put (pawnPosition .white).board (3, 2) ⟨.black, .knight⟩ }
      (.boardMove (3, 1) (3, 3) none) ∧
    ¬ PseudoLegal (pawnPosition .white) (.boardMove (3, 1) (3, 0) none) ∧
    ¬ PseudoLegal ⟨put kings (3, 2) ⟨.white, .pawn⟩, .white, {}, none⟩
      (.boardMove (3, 2) (3, 4) none) ∧
    ¬ PseudoLegal (pawnPosition .white) (.boardMove (3, 1) (2, 2) none) ∧
    ¬ PseudoLegal { (pawnPosition .white) with
        board := put (pawnPosition .white).board (3, 2) ⟨.black, .knight⟩ }
      (.boardMove (3, 1) (3, 2) none) := by
  decide

private def pawnCapture (c : Color) : Position :=
  { (pawnPosition c) with
    board := put (pawnPosition c).board (2, c.doubleStepTargetRank) ⟨c.opponent, .bishop⟩ }

example (c : Color) :
    LegalMove (pawnCapture c)
      (.boardMove (pawnStart c) (2, c.doubleStepTargetRank) none) kingHome ∧
    (applyMove (pawnCapture c)
      (.boardMove (pawnStart c) (2, c.doubleStepTargetRank) none)).board
      (2, c.doubleStepTargetRank) = some ⟨c, .pawn⟩ := by
  cases c <;> decide

-- Normal captures remove the victim. Own pieces and kings cannot be captured.
example :
    LegalMove ⟨put (put kings (0, 1) ⟨.white, .rook⟩) (0, 6) ⟨.black, .bishop⟩,
      .white, {}, none⟩ (.boardMove (0, 1) (0, 6) none) kingHome ∧
    ¬ PseudoLegal ⟨put (put kings (0, 1) ⟨.white, .rook⟩) (0, 6) ⟨.white, .bishop⟩,
      .white, {}, none⟩ (.boardMove (0, 1) (0, 6) none) ∧
    ¬ PseudoLegal ⟨put kings (4, 1) ⟨.white, .rook⟩, .white, {}, none⟩
      (.boardMove (4, 1) (4, 7) none) := by
  decide

private def promotionSource (c : Color) : Pos := (0, c.opponent.pawnRank)

private def promotionPosition (c : Color) : Position :=
  ⟨put kings (promotionSource c) ⟨c, .pawn⟩, c, {}, none⟩

example (c : Color) (q : Promotion) :
    LegalMove (promotionPosition c)
      (.boardMove (promotionSource c) (0, c.promotionRank) (some q)) kingHome ∧
    (applyMove (promotionPosition c)
      (.boardMove (promotionSource c) (0, c.promotionRank) (some q))).board
      (0, c.promotionRank) = some ⟨c, q.pieceType⟩ := by
  cases c <;> cases q <;> decide

-- The promoted piece attacks immediately using its new kind.
example (c : Color) (q : Promotion) :
    inCheck (applyMove (promotionPosition c)
      (.boardMove (promotionSource c) (0, c.promotionRank) (some q))).board
      c.opponent (kingHome c.opponent) ↔ q = .queen ∨ q = .rook := by
  cases c <;> cases q <;> decide

example (c : Color) (q : Promotion) :
    LegalMove
      { (promotionPosition c) with board := (put (promotionPosition c).board
          (1, c.promotionRank) ⟨c.opponent, .rook⟩) }
      (.boardMove (promotionSource c) (1, c.promotionRank) (some q)) kingHome := by
  cases c <;> cases q <;> decide

example (c : Color) :
    ¬ PseudoLegal (promotionPosition c)
      (.boardMove (promotionSource c) (0, c.promotionRank) none) ∧
    ¬ PseudoLegal (pawnPosition c)
      (.boardMove (pawnStart c) (pawnSingle c) (some .queen)) ∧
    ¬ PseudoLegal ⟨put kings (0, 1) ⟨c, .rook⟩, c, {}, none⟩
      (.boardMove (0, 1) (0, 2) (some .queen)) := by
  cases c <;> decide

example :
    ¬ PseudoLegal ⟨kings, .white, {}, none⟩ (.boardMove (0, 1) (0, 2) none) ∧
    ¬ PseudoLegal (pawnPosition .black) (.boardMove (4, 0) (5, 0) none) ∧
    ¬ PseudoLegal (pawnPosition .white) (.boardMove (3, 1) (3, 1) none) ∧
    ¬ LegalMove ⟨put kings (5, 7) ⟨.black, .rook⟩, .white, {}, none⟩
      (.boardMove (4, 0) (5, 0) none) kingHome ∧
    PseudoLegal ⟨put (put kings (4, 1) ⟨.white, .knight⟩) (4, 4) ⟨.black, .rook⟩,
      .white, {}, none⟩ (.boardMove (4, 1) (5, 3) none) ∧
    ¬ LegalMove ⟨put (put kings (4, 1) ⟨.white, .knight⟩) (4, 4) ⟨.black, .rook⟩,
      .white, {}, none⟩ (.boardMove (4, 1) (5, 3) none) kingHome := by
  decide

-- Each color's king actually moves, and the saved position follows it.
example (c : Color) :
    LegalMove ⟨kings, c, {}, none⟩ (.boardMove (kingHome c) (5, c.homeRank) none) kingHome ∧
    kingPositionsAfter kingHome c (.boardMove (kingHome c) (5, c.homeRank) none) c =
      (5, c.homeRank) ∧
    (applyMove ⟨kings, c, {}, none⟩
      (.boardMove (kingHome c) (5, c.homeRank) none)).board (kingHome c) = none := by
  cases c <;> decide

private def doubleBefore (c : Color) : Position :=
  { (pawnPosition c) with board := (put (pawnPosition c).board
      (4, c.opponent.enPassantRank) ⟨c.opponent, .pawn⟩) }

private def doubleAfter (c : Color) : Position :=
  applyMove (doubleBefore c) (.boardMove (pawnStart c) (pawnDouble c) none)

private def epReply (c : Color) : Move :=
  .enPassant (4, c.opponent.enPassantRank) (3, c.doubleStepTargetRank)

example (c : Color) :
    LegalMove (doubleBefore c) (.boardMove (pawnStart c) (pawnDouble c) none) kingHome ∧
    (doubleAfter c).enPassant = some (3, c.doubleStepTargetRank) ∧
    LegalMove (doubleAfter c) (epReply c) kingHome ∧
    (applyMove (doubleAfter c) (epReply c)).board (pawnDouble c) = none ∧
    (applyMove (doubleAfter c) (epReply c)).board (3, c.doubleStepTargetRank) =
      some ⟨c.opponent, .pawn⟩ ∧
    (applyMove (doubleAfter c) (epReply c)).enPassant = none := by
  cases c <;> decide

example (c : Color) :
    ¬ PseudoLegal { (doubleAfter c) with enPassant := none } (epReply c) ∧
    ¬ PseudoLegal { (doubleAfter c) with
      board := (doubleAfter c).board.erase (pawnDouble c) } (epReply c) ∧
    ¬ PseudoLegal { (doubleAfter c) with
      board := put (doubleAfter c).board (pawnDouble c) ⟨c, .knight⟩ } (epReply c) ∧
    ¬ PseudoLegal { (doubleAfter c) with
      board := put (doubleAfter c).board (3, c.doubleStepTargetRank) ⟨c, .bishop⟩ } (epReply c) ∧
    nextEnPassant (doubleAfter c)
      (.boardMove (kingHome c.opponent) (5, c.opponent.homeRank) none) = none := by
  cases c <;> decide

-- En passant can expose a rook attack through both removed pawns.
private def epPinBoard : Board := fun q =>
  if q = (4, 4) then some ⟨.white, .king⟩
  else if q = (0, 7) then some ⟨.black, .king⟩
  else if q = (5, 4) then some ⟨.white, .pawn⟩
  else if q = (6, 4) then some ⟨.black, .pawn⟩
  else if q = (7, 4) then some ⟨.black, .rook⟩ else none

private def epPinPosition : Position := ⟨epPinBoard, .white, {}, some (6, 5)⟩

example : PseudoLegal epPinPosition (.enPassant (5, 4) (6, 5)) ∧
    ¬ inCheck epPinBoard .white (4, 4) ∧
    inCheck (applyMove epPinPosition (.enPassant (5, 4) (6, 5))).board .white (4, 4) ∧
    ¬ LegalMove epPinPosition (.enPassant (5, 4) (6, 5))
      (fun c => if c = .white then (4, 4) else (0, 7)) := by
  decide

private def castlePosition (c : Color) (side : CastleSide) : Position :=
  ⟨put kings (rookHome c side) ⟨c, .rook⟩, c, allRights, none⟩

example (c : Color) (side : CastleSide) :
    LegalMove (castlePosition c side) (.castle side) kingHome ∧
    kingPositionsAfter kingHome c (.castle side) c = castleKingDestination c side ∧
    kingPositionsAfter kingHome c (.castle side) c.opponent = kingHome c.opponent ∧
    (applyMove (castlePosition c side) (.castle side)).board (kingHome c) = none ∧
    (applyMove (castlePosition c side) (.castle side)).board (rookHome c side) = none ∧
    (applyMove (castlePosition c side) (.castle side)).board (castleKingDestination c side) =
      some ⟨c, .king⟩ ∧
    (applyMove (castlePosition c side) (.castle side)).board (castleRookDestination c side) =
      some ⟨c, .rook⟩ ∧
    (applyMove (castlePosition c side) (.castle side)).castlingRights.allows c .kingSide = false ∧
    (applyMove (castlePosition c side) (.castle side)).castlingRights.allows c .queenSide = false ∧
    (applyMove (castlePosition c side) (.castle side)).castlingRights.allows c.opponent .kingSide = true ∧
    (applyMove (castlePosition c side) (.castle side)).castlingRights.allows c.opponent .queenSide = true := by
  cases c <;> cases side <;> decide

example (c : Color) (side : CastleSide) :
    ¬ PseudoLegal { (castlePosition c side) with castlingRights := {} } (.castle side) ∧
    ¬ PseudoLegal ⟨kings, c, allRights, none⟩ (.castle side) ∧
    ¬ PseudoLegal { (castlePosition c side) with board :=
      (put (castlePosition c side).board (castleRookDestination c side) ⟨c, .knight⟩) }
      (.castle side) := by
  cases c <;> cases side <;> decide

-- Starting, crossing, and landing in attack each forbid castling. The extra
-- b-file square on the queenside must also be vacant.
example :
    (∀ file ∈ ([4, 5, 6] : List (Fin 8)),
      ¬ PseudoLegal { (castlePosition .white .kingSide) with board :=
        (put (castlePosition .white .kingSide).board (file, 4) ⟨.black, .rook⟩) }
        (.castle .kingSide)) ∧
    (∀ file ∈ ([4, 3, 2] : List (Fin 8)),
      ¬ PseudoLegal { (castlePosition .black .queenSide) with board :=
        (put (castlePosition .black .queenSide).board (file, 3) ⟨.white, .rook⟩) }
        (.castle .queenSide)) ∧
    ¬ PseudoLegal { (castlePosition .white .queenSide) with board :=
      (put (castlePosition .white .queenSide).board (1, 0) ⟨.white, .knight⟩) }
      (.castle .queenSide) := by
  decide

-- Rights are lost by a king move, by a home-rook move, and by capture of a home rook.
example :
    let p : Position := ⟨put (put kings (0, 0) ⟨.white, .rook⟩) (0, 7) ⟨.black, .rook⟩,
      .white, allRights, none⟩
    LegalMove p (.boardMove (0, 0) (0, 7) none) kingHome ∧
    (applyMove p (.boardMove (0, 0) (0, 7) none)).castlingRights.whiteQueenSide = false ∧
    (applyMove p (.boardMove (0, 0) (0, 7) none)).castlingRights.blackQueenSide = false ∧
    (applyMove p (.boardMove (0, 0) (0, 7) none)).castlingRights.whiteKingSide = true ∧
    (applyMove p (.boardMove (0, 0) (0, 7) none)).castlingRights.blackKingSide = true ∧
    (applyMove p (.boardMove (4, 0) (5, 0) none)).castlingRights.whiteKingSide = false ∧
    (applyMove p (.boardMove (4, 0) (5, 0) none)).castlingRights.whiteQueenSide = false := by
  decide

example (pos : Position) (move : Move) (kp : Color → Pos) (h : LegalMove pos move kp) :
    (MoveTrace.single pos (applyMove pos move) move).FollowsLegalMoves := by
  apply (MoveTrace.single_follows_iff pos (applyMove pos move) move LegalTransition).mpr
  exact ⟨kp, h, rfl⟩

end MPC.Chess.Tests
