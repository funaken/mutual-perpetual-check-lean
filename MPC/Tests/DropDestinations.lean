import MPC.Invariants.DropDestinations
import Lean
/-!
# MPC.Tests.DropDestinations

Concrete checks for .

- The family of all types counts every piece: a board with a first-player rook in
  hand and a second-player bishop on `(4, 4)` has total `2`.
- Dropping the rook onto the bishop's square overwrites it: the total goes from `2`
  to `1`. Dropping it onto an empty square keeps it at `2`.
- Periodicity is needed: the one-move trace that drops the rook onto the bishop
  satisfies `DropsFromHand` but not `DropDestinationsEmpty`. It is not periodic, so
  `dropDestinationsEmpty_of_dropsFromHand` does not apply to it.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Drop destinations verification must not import GameSeq"

namespace MPC
namespace DropDestinationsTests

open MoveTrace

/-- A second-player bishop on `(4, 4)`, and nothing else on the board. -/
private def bishopGrid : Pos → Square := fun q =>
  if q = (4, 4) then some ⟨.gote, .bishop⟩ else none

/-- That board, the first player to move, with a rook in the first player's hand. -/
private def rookInHand : BoardState :=
  { board := { grid := bishopGrid, hand := fun p => if p = .sente then {.rook} else ∅ },
    turn := .sente }

/-! ## Counting every piece -/

example : rookInHand.board.familyTotal PieceType.IsAny = 2 := by decide

-- Onto the bishop: the bishop is overwritten and lost.
example : (applyMove rookInHand (.dropMove .rook (4, 4))).board.familyTotal
    PieceType.IsAny = 1 := by decide

-- Onto an empty square: the rook only moves from the hand to the board.
example : (applyMove rookInHand (.dropMove .rook (0, 0))).board.familyTotal
    PieceType.IsAny = 2 := by decide

/-! ## Periodicity is needed -/

/-- The one-move trace that drops the rook onto the bishop. -/
private abbrev overwriteTrace : MoveTrace :=
  MoveTrace.single rookInHand (.dropMove .rook (4, 4))

/-- Its only move. -/
private abbrev m0 : Fin overwriteTrace.len := ⟨0, Nat.zero_lt_one⟩

example : overwriteTrace.DropsFromHand := by
  intro i pt dst hm
  have hi : i.val = 0 := by
    have := i.isLt
    change i.val < 1 at this
    omega
  change Move.dropMove .rook (4, 4) = .dropMove pt dst at hm
  rw [Move.dropMove.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  obtain rfl : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext hi
  simp [MoveTrace.before, MoveTrace.single, overwriteTrace, rookInHand]

example : ¬ overwriteTrace.DropDestinationsEmpty := by
  intro h
  have := h m0 .rook (4, 4) rfl
  simp [MoveTrace.before, MoveTrace.single, overwriteTrace, m0, rookInHand, bishopGrid] at this

end DropDestinationsTests
end MPC
