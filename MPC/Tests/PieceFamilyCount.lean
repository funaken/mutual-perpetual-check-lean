import MPC.Invariants.PieceFamilyCount
import Lean
/-!
# MPC.Tests.PieceFamilyCount

Concrete checks for .

- Promotion keeps the families: a promoted bishop is a horse (bishop family), a
  promoted silver is outside it.
- Counts: a board with a first-player bishop on `(0, 0)` and a horse in the second
  player's hand has one bishop-family square, one bishop-family piece in hand, and
  bishop-family total `2`; its rook-family total is `0`.
- `InitialPieceCountsAtMostTwo` holds for that board, and fails when a second bishop
  is added on `(8, 8)` (total `3`).
- `DropsFromHand` on one-move traces: dropping a pawn from a hand that holds one
  satisfies it; dropping from an empty hand does not. The model's `applyMove` makes
  both moves, so the premise is a real restriction.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Piece family count verification must not import GameSeq"

namespace MPC
namespace PieceFamilyCountTests

open MoveTrace

/-! ## Promotion keeps the families -/

example : PieceType.IsBishopFamily PieceType.bishop.promote := by decide
example : ¬ PieceType.IsBishopFamily PieceType.silver.promote := by decide
example : PieceType.IsRookFamily PieceType.rook.promote := by decide

/-! ## Counts on the board and in hand -/

/-- A first-player bishop on `(0, 0)`, nothing else on the board. -/
private def bishopGrid : Pos → Square := fun q =>
  if q = (0, 0) then some ⟨.sente, .bishop⟩ else none

/-- That board, with a horse in the second player's hand. -/
private def bishopBoard : Board :=
  { grid := bishopGrid, hand := fun p => if p = .gote then {.horse} else ∅ }

example : bishopBoard.familyCount PieceType.IsBishopFamily = 1 := by decide
example : bishopBoard.handFamilyCount PieceType.IsBishopFamily = 1 := by decide
example : bishopBoard.familyTotal PieceType.IsBishopFamily = 2 := by decide
example : bishopBoard.familyTotal PieceType.IsRookFamily = 0 := by decide

/-! ## The initial counts -/

private def oneState (b : Board) : MoveTrace :=
  { len := 0, states := fun _ => { board := b, turn := .sente }, moves := Fin.elim0 }

example : (oneState bishopBoard).InitialPieceCountsAtMostTwo := by
  constructor <;> decide

/-- A second bishop on `(8, 8)`. -/
private def threeBishopBoard : Board :=
  { grid := fun q => if q = (8, 8) then some ⟨.gote, .bishop⟩ else bishopGrid q,
    hand := bishopBoard.hand }

example : ¬ (oneState threeBishopBoard).InitialPieceCountsAtMostTwo := by
  rintro ⟨h, _⟩
  have : threeBishopBoard.familyTotal PieceType.IsBishopFamily = 3 := by decide
  exact absurd (this ▸ h) (by decide)

/-! ## Drops from the hand -/

/-- An empty board, the first player to move, with the given first-player hand. -/
private def handState (h : Hand) : BoardState :=
  { board := { grid := fun _ => none, hand := fun p => if p = .sente then h else ∅ },
    turn := .sente }

/-- The one move of a one-move trace. -/
private abbrev m0 {s : BoardState} {m : Move} : Fin (MoveTrace.single s m).len :=
  ⟨0, Nat.zero_lt_one⟩

-- A pawn in hand: the drop satisfies the premise.
example : (MoveTrace.single (handState {.pawn}) (.dropMove .pawn (4, 4))).DropsFromHand := by
  intro i pt dst hm
  have hi : i.val = 0 := by
    have := i.isLt
    change i.val < 1 at this
    omega
  change Move.dropMove .pawn (4, 4) = .dropMove pt dst at hm
  rw [Move.dropMove.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  obtain rfl : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext hi
  simp [MoveTrace.before, MoveTrace.single, handState]

-- An empty hand: the same drop violates it, though `applyMove` still makes it.
example : ¬ (MoveTrace.single (handState ∅) (.dropMove .pawn (4, 4))).DropsFromHand := by
  intro h
  have := h m0 .pawn (4, 4) rfl
  simp [MoveTrace.before, MoveTrace.single, handState, m0] at this

end PieceFamilyCountTests
end MPC
