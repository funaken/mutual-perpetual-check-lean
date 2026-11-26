import MPC.Chess.Trace

/-! Local movement conditions and total board updates for standard chess.
`PseudoLegal` excludes king captures and own-piece captures. It does not enforce
final king safety; `LegalMove` adds that condition in the preservation module.
Rights/EP data describe history supplied at the start of a trace. Reachability
from the standard initial position is a separate property. -/

namespace MPC.Chess

def Color.homeRank : Color → Fin 8
  | .white => 0
  | .black => 7

def Color.pawnRank : Color → Fin 8
  | .white => 1
  | .black => 6

def Color.promotionRank (c : Color) : Fin 8 := c.opponent.homeRank

def Color.enPassantRank : Color → Fin 8
  | .white => 4
  | .black => 3

def Color.doubleStepTargetRank : Color → Fin 8
  | .white => 2
  | .black => 5

def kingHome (c : Color) : Pos := (4, c.homeRank)

def rookHome (c : Color) (side : CastleSide) : Pos :=
  (match side with | .kingSide => 7 | .queenSide => 0, c.homeRank)

def castleKingDestination (c : Color) (side : CastleSide) : Pos :=
  (match side with | .kingSide => 6 | .queenSide => 2, c.homeRank)

def castleRookDestination (c : Color) (side : CastleSide) : Pos :=
  (match side with | .kingSide => 5 | .queenSide => 3, c.homeRank)

def CastlingRights.allows (r : CastlingRights) (c : Color) (side : CastleSide) : Bool :=
  match c, side with
  | .white, .kingSide => r.whiteKingSide
  | .white, .queenSide => r.whiteQueenSide
  | .black, .kingSide => r.blackKingSide
  | .black, .queenSide => r.blackQueenSide

def CastlingRights.ofFunction (f : Color → CastleSide → Bool) : CastlingRights :=
  ⟨f .white .kingSide, f .white .queenSide, f .black .kingSide, f .black .queenSide⟩

@[simp] theorem CastlingRights.allows_ofFunction (f : Color → CastleSide → Bool)
    (c : Color) (side : CastleSide) : (ofFunction f).allows c side = f c side := by
  cases c <;> cases side <;> rfl

def CastlingRights.disable (r : CastlingRights) (owner : Color) : CastlingRights :=
  .ofFunction fun c side => if c = owner then false else r.allows c side

/-- Moving a king/rook or capturing a home rook irrevocably loses its rights. -/
def CastlingRights.afterBoardMove (r : CastlingRights) (b : Board) (src dst : Pos) :
    CastlingRights :=
  .ofFunction fun c side =>
    if b src = some ⟨c, .king⟩ ∨
        (src = rookHome c side ∧ b src = some ⟨c, .rook⟩) ∨
        (dst = rookHome c side ∧ b dst = some ⟨c, .rook⟩)
    then false else r.allows c side

/-- The update leaves non-pawns unchanged even for malformed move data.
`PromotionAllowed` separately rejects such a promotion request. -/
def Piece.promote (p : Piece) (choice : Option Promotion) : Piece :=
  match choice with
  | none => p
  | some q => if p.kind = .pawn then ⟨p.owner, q.pieceType⟩ else p

@[simp] theorem Piece.promote_eq_king_iff (p : Piece) (choice : Option Promotion)
    (owner : Color) : p.promote choice = ⟨owner, .king⟩ ↔ p = ⟨owner, .king⟩ := by
  rcases p with ⟨c, kind⟩
  cases choice with
  | none => rfl
  | some q => cases kind <;> cases q <;> simp [Piece.promote, Promotion.pieceType]

def Board.relocate (b : Board) (src dst : Pos) (choice : Option Promotion := none) : Board :=
  fun q => if q = dst then (b src).map (·.promote choice) else if q = src then none else b q

def Board.erase (b : Board) (pos : Pos) : Board := fun q => if q = pos then none else b q

@[simp] theorem Board.relocate_destination (b : Board) (src dst : Pos)
    (choice : Option Promotion) :
    b.relocate src dst choice dst = (b src).map (·.promote choice) := by
  simp [Board.relocate]

theorem Board.relocate_source (b : Board) (src dst : Pos) (choice : Option Promotion)
    (h : src ≠ dst) : b.relocate src dst choice src = none := by
  simp [Board.relocate, h]

theorem Board.relocate_other (b : Board) (src dst q : Pos) (choice : Option Promotion)
    (hs : q ≠ src) (hd : q ≠ dst) : b.relocate src dst choice q = b q := by
  simp [Board.relocate, hs, hd]

def enPassantCaptured (src dst : Pos) : Pos := (dst.1, src.2)

def applyBoard (b : Board) (turn : Color) : Move → Board
  | .boardMove src dst choice => b.relocate src dst choice
  | .enPassant src dst => (b.erase (enPassantCaptured src dst)).relocate src dst none
  | .castle side => (b.relocate (kingHome turn) (castleKingDestination turn side) none).relocate
      (rookHome turn side) (castleRookDestination turn side) none

def DestinationAvailable (b : Board) (turn : Color) (dst : Pos) : Prop :=
  match b dst with
  | none => True
  | some p => p.owner = turn.opponent ∧ p.kind ≠ .king

instance (b : Board) (turn : Color) (dst : Pos) : Decidable (DestinationAvailable b turn dst) :=
  by unfold DestinationAvailable; cases b dst <;> infer_instance

def PromotionAllowed (p : Piece) (dst : Pos) : Option Promotion → Prop
  | none => ¬ (p.kind = .pawn ∧ dst.2 = p.owner.promotionRank)
  | some _ => p.kind = .pawn ∧ dst.2 = p.owner.promotionRank

instance (p : Piece) (dst : Pos) (choice : Option Promotion) :
    Decidable (PromotionAllowed p dst choice) := by
  cases choice <;> unfold PromotionAllowed <;> infer_instance

/-- Non-capture pawn pushes and diagonal captures are different branches. -/
def PawnMovement (b : Board) (c : Color) (src dst : Pos) : Prop :=
  0 < src.2.val ∧ src.2.val < 7 ∧
  ((b dst = none ∧ (Pos.delta src dst).1 = 0 ∧
    ((Pos.delta src dst).2 = c.forward ∨
      (src.2 = c.pawnRank ∧ (Pos.delta src dst).2 = 2 * c.forward ∧ pathClear b src dst))) ∨
   (b dst ≠ none ∧ attacks b ⟨c, .pawn⟩ src dst))

def OrdinaryMovement (b : Board) (p : Piece) (src dst : Pos) : Prop :=
  if p.kind = .pawn then PawnMovement b p.owner src dst else attacks b p src dst

def CastleAllowed (pos : Position) (side : CastleSide) : Prop :=
  pos.castlingRights.allows pos.turn side = true ∧
  pos.board (kingHome pos.turn) = some ⟨pos.turn, .king⟩ ∧
  pos.board (rookHome pos.turn side) = some ⟨pos.turn, .rook⟩ ∧
  pathClear pos.board (kingHome pos.turn) (rookHome pos.turn side) ∧
  ¬ inCheck pos.board pos.turn (kingHome pos.turn) ∧
  ¬ inCheck pos.board pos.turn (castleRookDestination pos.turn side) ∧
  ¬ inCheck pos.board pos.turn (castleKingDestination pos.turn side)

def PseudoLegal (pos : Position) : Move → Prop
  | .boardMove src dst choice =>
    ∃ p, pos.board src = some p ∧ p.owner = pos.turn ∧ src ≠ dst ∧
      DestinationAvailable pos.board pos.turn dst ∧ PromotionAllowed p dst choice ∧
      OrdinaryMovement pos.board p src dst
  | .enPassant src dst =>
    pos.board src = some ⟨pos.turn, .pawn⟩ ∧ pos.board dst = none ∧
    pos.enPassant = some dst ∧ src.2 = pos.turn.enPassantRank ∧
    attacks pos.board ⟨pos.turn, .pawn⟩ src dst ∧
    pos.board (enPassantCaptured src dst) = some ⟨pos.turn.opponent, .pawn⟩
  | .castle side => CastleAllowed pos side

instance (b : Board) (c : Color) (src dst : Pos) : Decidable (PawnMovement b c src dst) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ((_ ∧ _ ∧ (_ ∨ (_ ∧ _ ∧ _))) ∨ (_ ∧ _))))

instance (b : Board) (p : Piece) (src dst : Pos) : Decidable (OrdinaryMovement b p src dst) :=
  by unfold OrdinaryMovement; split <;> infer_instance

instance (pos : Position) (side : CastleSide) : Decidable (CastleAllowed pos side) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

instance (pos : Position) (move : Move) : Decidable (PseudoLegal pos move) := by
  cases move <;> unfold PseudoLegal <;> infer_instance

def nextEnPassant (pos : Position) : Move → Option Pos
  | .boardMove src dst none =>
    if pos.board src = some ⟨pos.turn, .pawn⟩ ∧ src.2 = pos.turn.pawnRank ∧
      Pos.delta src dst = (0, 2 * pos.turn.forward)
    then some (src.1, pos.turn.doubleStepTargetRank) else none
  | _ => none

def nextCastlingRights (pos : Position) : Move → CastlingRights
  | .boardMove src dst _ => pos.castlingRights.afterBoardMove pos.board src dst
  | .enPassant _ _ => pos.castlingRights
  | .castle _ => pos.castlingRights.disable pos.turn

def applyMove (pos : Position) (move : Move) : Position where
  board := applyBoard pos.board pos.turn move
  turn := pos.turn.opponent
  castlingRights := nextCastlingRights pos move
  enPassant := nextEnPassant pos move

@[simp] theorem applyMove_turn (pos : Position) (move : Move) :
    (applyMove pos move).turn = pos.turn.opponent := rfl

/-- A nonempty EP target records exactly the immediately preceding double push.
The hypothesis `PseudoLegal` is needed separately to make that push legal. -/
theorem nextEnPassant_eq_some_iff (pos : Position) (move : Move) (target : Pos) :
    nextEnPassant pos move = some target ↔
      ∃ src dst, move = .boardMove src dst none ∧
        pos.board src = some ⟨pos.turn, .pawn⟩ ∧ src.2 = pos.turn.pawnRank ∧
        Pos.delta src dst = (0, 2 * pos.turn.forward) ∧
        target = (src.1, pos.turn.doubleStepTargetRank) := by
  constructor
  · intro h
    cases move with
    | boardMove src dst choice =>
      cases choice with
      | none =>
        simp only [nextEnPassant] at h
        split at h
        · rename_i hp
          exact ⟨src, dst, rfl, hp.1, hp.2.1, hp.2.2, (Option.some.inj h).symm⟩
        · contradiction
      | some q => simp [nextEnPassant] at h
    | enPassant src dst => simp [nextEnPassant] at h
    | castle side => simp [nextEnPassant] at h
  · rintro ⟨src, dst, rfl, hs, hr, hd, rfl⟩
    simp [nextEnPassant, hs, hr, hd]

theorem applyMove_castlingRights_no_gain (pos : Position) (move : Move)
    (c : Color) (side : CastleSide)
    (h : (applyMove pos move).castlingRights.allows c side = true) :
    pos.castlingRights.allows c side = true := by
  cases move with
  | boardMove src dst choice =>
    simp only [applyMove, nextCastlingRights, CastlingRights.afterBoardMove,
      CastlingRights.allows_ofFunction] at h
    split at h
    · contradiction
    · exact h
  | enPassant src dst => exact h
  | castle cs =>
    simp only [applyMove, nextCastlingRights, CastlingRights.disable,
      CastlingRights.allows_ofFunction] at h
    split at h
    · contradiction
    · exact h

end MPC.Chess
