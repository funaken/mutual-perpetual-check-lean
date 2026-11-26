import MPC.Trace.MutualCheck
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
/-!
# MPC.Invariants.PieceFamilyCount

Piece counts on the board and in hand, and the two premises that replace
`PieceCountsAtMostTwo`.

The trace model's `applyMove` drops a piece without checking the hand, so the
number of bishops on the board does not follow from the transitions. Shogi's rules give two
conditions instead:

- `MoveTrace.DropsFromHand`: a drop's piece type is in the mover's hand before the
  move.
- `MoveTrace.InitialPieceCountsAtMostTwo`: in state 0, the board and both hands hold
  at most two bishops or horses together, and at most two rooks or dragons.

Pieces are counted by family: `PieceType.IsBishopFamily` (bishop, horse) and
`PieceType.IsRookFamily` (rook, dragon). Promotion never moves a type into or out of
either family (`PromoteStable`), and a captured piece enters the hand as its original
piece, which is in the same family (`PromoteStable.demote_iff`), so these
families are what a move preserves.

- `Board.familyCount`: the squares holding a piece of the family, as a sum of
  indicators (`familyInd`) over all squares.
- `Board.handFamilyCount`: the pieces of the family in both hands.
- `Board.familyTotal`: their sum.
- `bishopHorseSquares_card_eq`, `rookDragonSquares_card_eq`: the board counts are
  the cards that `PieceCountsAtMostTwo` bounds.

-/

namespace MPC

/-- The bishop family: a bishop or a horse. -/
def PieceType.IsBishopFamily (pt : PieceType) : Prop := pt = .bishop ∨ pt = .horse

/-- The rook family: a rook or a dragon. -/
def PieceType.IsRookFamily (pt : PieceType) : Prop := pt = .rook ∨ pt = .dragon

instance : DecidablePred PieceType.IsBishopFamily := fun pt =>
  inferInstanceAs (Decidable (pt = .bishop ∨ pt = .horse))

instance : DecidablePred PieceType.IsRookFamily := fun pt =>
  inferInstanceAs (Decidable (pt = .rook ∨ pt = .dragon))

/-- Promotion keeps a piece type inside `F` or outside it. -/
def PromoteStable (F : PieceType → Prop) : Prop := ∀ pt : PieceType, F pt.promote ↔ F pt

theorem promoteStable_bishopFamily : PromoteStable PieceType.IsBishopFamily := by
  intro pt
  cases pt <;> decide

theorem promoteStable_rookFamily : PromoteStable PieceType.IsRookFamily := by
  intro pt
  cases pt <;> decide

/-- `1` for a square holding a piece of the family `F`, `0` otherwise. -/
def familyInd (F : PieceType → Prop) [DecidablePred F] : Option Piece → ℕ
  | some p => if F p.pieceType then 1 else 0
  | none => 0

/-- The number of squares holding a piece of the family `F`. -/
def Board.familyCount (b : Board) (F : PieceType → Prop) [DecidablePred F] : ℕ :=
  ∑ q : Pos, familyInd F (b.grid q)

/-- The number of pieces of the family `F` in both hands. -/
def Board.handFamilyCount (b : Board) (F : PieceType → Prop) [DecidablePred F] : ℕ :=
  Multiset.countP F (b.hand .sente) + Multiset.countP F (b.hand .gote)

/-- The pieces of the family `F` on the board and in both hands. -/
def Board.familyTotal (b : Board) (F : PieceType → Prop) [DecidablePred F] : ℕ :=
  b.familyCount F + b.handFamilyCount F

theorem Board.familyCount_le_familyTotal (b : Board) (F : PieceType → Prop)
    [DecidablePred F] : b.familyCount F ≤ b.familyTotal F :=
  Nat.le_add_right _ _

namespace MoveTrace

/-- Drops come from the hand: a drop's piece type is in the mover's hand before the
    move. -/
def DropsFromHand (tr : MoveTrace) : Prop :=
  ∀ (i : Fin tr.len) (pt : PieceType) (dst : Pos),
    tr.moves i = .dropMove pt dst → pt ∈ (tr.before i).board.hand (tr.before i).turn

/-- In state 0 the board and both hands hold at most two bishops or horses together,
    and at most two rooks or dragons. -/
def InitialPieceCountsAtMostTwo (tr : MoveTrace) : Prop :=
  (tr.states 0).board.familyTotal PieceType.IsBishopFamily ≤ 2 ∧
    (tr.states 0).board.familyTotal PieceType.IsRookFamily ≤ 2

/-- The squares holding a bishop or a horse are counted by the bishop family. -/
theorem bishopHorseSquares_card_eq (tr : MoveTrace) (k : Fin (tr.len + 1)) :
    (tr.bishopHorseSquares k).card = (tr.states k).board.familyCount PieceType.IsBishopFamily := by
  rw [bishopHorseSquares, Finset.card_filter]
  unfold Board.familyCount
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases (tr.states k).board.grid q with _ | p
  · simp [familyInd]
  · simp [familyInd, PieceType.IsBishopFamily]
    congr

/-- The squares holding a rook or a dragon are counted by the rook family. -/
theorem rookDragonSquares_card_eq (tr : MoveTrace) (k : Fin (tr.len + 1)) :
    (tr.rookDragonSquares k).card = (tr.states k).board.familyCount PieceType.IsRookFamily := by
  rw [rookDragonSquares, Finset.card_filter]
  unfold Board.familyCount
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases (tr.states k).board.grid q with _ | p
  · simp [familyInd]
  · simp [familyInd, PieceType.IsRookFamily]
    congr

end MoveTrace
end MPC
