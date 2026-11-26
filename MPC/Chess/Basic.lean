import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-! Independent data for standard chess. Files/ranks are numbered 0 through 7;
White advances toward increasing ranks. No validity conditions are built into
positions or moves. In particular, castling rights and en-passant information
are data whose consistency must be checked by a transition relation. -/

namespace MPC.Chess

inductive Color where
  | white | black
  deriving DecidableEq, Repr

instance : Fintype Color := ⟨{.white, .black}, fun c => by cases c <;> simp⟩

def Color.opponent : Color → Color
  | .white => .black
  | .black => .white

@[simp] theorem Color.opponent_opponent (c : Color) : c.opponent.opponent = c := by
  cases c <;> rfl

@[simp] theorem Color.opponent_ne (c : Color) : c.opponent ≠ c := by
  cases c <;> decide

def Color.forward : Color → ℤ
  | .white => 1
  | .black => -1

inductive PieceType where
  | king | queen | rook | bishop | knight | pawn
  deriving DecidableEq, Repr

instance : Fintype PieceType :=
  ⟨{.king, .queen, .rook, .bishop, .knight, .pawn}, fun k => by cases k <;> simp⟩

structure Piece where
  owner : Color
  kind : PieceType
  deriving DecidableEq, Repr

instance : Fintype Piece :=
  Fintype.ofEquiv (Color × PieceType)
    ⟨fun x => ⟨x.1, x.2⟩, fun p => (p.owner, p.kind), fun _ => rfl, fun _ => rfl⟩

abbrev Pos := Fin 8 × Fin 8

def Pos.toInt (p : Pos) : ℤ × ℤ := (p.1.val, p.2.val)

def Pos.delta (src dst : Pos) : ℤ × ℤ :=
  (dst.toInt.1 - src.toInt.1, dst.toInt.2 - src.toInt.2)

abbrev Board := Pos → Option Piece

def Board.empty : Board := fun _ => none

inductive CastleSide where
  | kingSide | queenSide
  deriving DecidableEq, Repr

instance : Fintype CastleSide := ⟨{.kingSide, .queenSide}, fun s => by cases s <;> simp⟩

structure CastlingRights where
  whiteKingSide : Bool := false
  whiteQueenSide : Bool := false
  blackKingSide : Bool := false
  blackQueenSide : Bool := false
  deriving DecidableEq, Repr

structure Position where
  board : Board
  turn : Color
  castlingRights : CastlingRights := {}
  enPassant : Option Pos := none

/-- Promotion cannot produce a king or another pawn. -/
inductive Promotion where
  | queen | rook | bishop | knight
  deriving DecidableEq, Repr

instance : Fintype Promotion :=
  ⟨{.queen, .rook, .bishop, .knight}, fun q => by cases q <;> simp⟩

def Promotion.pieceType : Promotion → PieceType
  | .queen => .queen
  | .rook => .rook
  | .bishop => .bishop
  | .knight => .knight

inductive Move where
  | boardMove (src dst : Pos) (promotion : Option Promotion := none)
  | enPassant (src dst : Pos)
  | castle (side : CastleSide)
  deriving DecidableEq, Repr

end MPC.Chess
