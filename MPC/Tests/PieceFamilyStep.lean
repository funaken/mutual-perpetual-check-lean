import MPC.Invariants.PieceFamilyStep
import Lean
/-!
# MPC.Tests.PieceFamilyStep

Concrete checks for , by evaluating `applyMove` on small boards.

- A capture keeps the bishop-family total: a first-player bishop on `(0, 0)` takes a
  second-player horse on `(1, 1)` and promotes. Before, the total is `2` (both on the
  board); after, it is still `2` (a horse on the board, a horse in hand).
- A drop from the hand keeps the total: dropping a bishop held in hand onto an empty
  square moves it from the hand to the board.
- A drop onto an occupied square lowers it: dropping a rook from hand onto a bishop's
  square removes the bishop.
- Without `DropsFromHand` the total can rise: `applyMove` drops a bishop from an
  empty hand, and the total goes from `0` to `1`. So the premise is needed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Piece family step verification must not import GameSeq"

namespace MPC
namespace PieceFamilyStepTests

/-- A board with the given squares and the first player's hand. -/
private def board (g : Pos → Square) (h : Hand) : BoardState :=
  { board := { grid := g, hand := fun p => if p = .sente then h else ∅ }, turn := .sente }

/-! ## A capture -/

private def captureGrid : Pos → Square := fun q =>
  if q = (0, 0) then some ⟨.sente, .bishop⟩
  else if q = (1, 1) then some ⟨.gote, .horse⟩
  else none

example : (board captureGrid ∅).board.familyTotal PieceType.IsBishopFamily = 2 := by decide
example : (applyMove (board captureGrid ∅) (.boardMove (0, 0) (1, 1) true)).board.familyTotal
    PieceType.IsBishopFamily = 2 := by decide
example : (applyMove (board captureGrid ∅) (.boardMove (0, 0) (1, 1) true)).board.familyCount
    PieceType.IsBishopFamily = 1 := by decide

/-! ## Drops -/

-- From the hand onto an empty square: the total stays `1`.
example : (board (fun _ => none) {.bishop}).board.familyTotal PieceType.IsBishopFamily = 1 := by
  decide
example : (applyMove (board (fun _ => none) {.bishop}) (.dropMove .bishop (4, 4))).board.familyTotal
    PieceType.IsBishopFamily = 1 := by decide

-- Onto an occupied square: the overwritten bishop is lost.
private def bishopOn44 : Pos → Square := fun q =>
  if q = (4, 4) then some ⟨.gote, .bishop⟩ else none

example : (board bishopOn44 {.rook}).board.familyTotal PieceType.IsBishopFamily = 1 := by decide
example : (applyMove (board bishopOn44 {.rook}) (.dropMove .rook (4, 4))).board.familyTotal
    PieceType.IsBishopFamily = 0 := by decide

-- From an empty hand (not `DropsFromHand`): the total rises from `0` to `1`.
example : (board (fun _ => none) ∅).board.familyTotal PieceType.IsBishopFamily = 0 := by decide
example : (applyMove (board (fun _ => none) ∅) (.dropMove .bishop (4, 4))).board.familyTotal
    PieceType.IsBishopFamily = 1 := by decide

end PieceFamilyStepTests
end MPC
