import MPC.Invariants.DiscoveredCheckNecessity
import Lean
/-!
# MPC.Tests.DiscoveredCheckNecessity

Concrete checks for .

- Hands (`hand_card_succ_of_capture`, `hand_card_succ_of_turn_ne`): on a one-move
  trace where a first-player rook on `(0, 0)` takes a second-player pawn on
  `(0, 1)`, the first player's hand grows by one and the second player's does not
  change.
- `eq_of_step_le_of_last_eq`: a sequence that falls once and does not come back has
  a falling step, so the premise `f (Fin.last n) = f 0` is needed; a constant
  sequence satisfies both premises.

Proposition 4.1 itself is not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Discovered-check necessity verification must not import GameSeq"

namespace MPC
namespace DiscoveredCheckNecessityTests

open MoveTrace

/-- A first-player rook on `(0, 0)` and a second-player pawn on `(0, 1)`, empty hands. -/
private def captureGrid : Pos → Square := fun q =>
  if q = (0, 0) then some ⟨.sente, .rook⟩
  else if q = (0, 1) then some ⟨.gote, .pawn⟩
  else none

private def captureState : BoardState :=
  { board := { grid := captureGrid, hand := fun _ => ∅ }, turn := .sente }

private abbrev captureMove : Move := .boardMove (0, 0) (0, 1) false

private abbrev captureTrace : MoveTrace := MoveTrace.single captureState captureMove

/-- Its only move. -/
private abbrev m0 : Fin captureTrace.len := ⟨0, Nat.zero_lt_one⟩

/-! ## Hands -/

-- The rook takes the pawn: the first player's hand grows by one.
example : Multiset.card ((captureTrace.after m0).board.hand .sente) =
    Multiset.card ((captureTrace.before m0).board.hand .sente) + 1 :=
  captureTrace.hand_card_succ_of_capture (single_followsTransitions _ _) m0 (0, 0) (0, 1) false rfl
    ⟨.gote, .pawn⟩
    (by simp [captureTrace, MoveTrace.before, MoveTrace.single, captureState, captureGrid, m0])

-- The second player's hand is left alone.
example : Multiset.card ((captureTrace.after m0).board.hand .gote) =
    Multiset.card ((captureTrace.before m0).board.hand .gote) :=
  captureTrace.hand_card_succ_of_turn_ne (single_followsTransitions _ _) m0 .gote
    (by simp [captureTrace, MoveTrace.before, MoveTrace.single, captureState, m0])

/-! ## Sequences that never rise -/

/-- A sequence that falls once and does not come back. -/
private def falling : Fin 3 → ℚ := fun k => if k.val = 0 then 2 else 1

-- Without `f (Fin.last n) = f 0` a step can fall.
example : falling (0 : Fin 2).succ ≠ falling (0 : Fin 2).castSucc ∧
    falling (Fin.last 2) ≠ falling 0 := by
  norm_num [falling]

-- A constant sequence satisfies both premises.
private def constant : Fin 3 → ℚ := fun _ => 1

example (i : Fin 2) : constant i.succ = constant i.castSucc :=
  eq_of_step_le_of_last_eq constant (fun _ => le_rfl) rfl i

end DiscoveredCheckNecessityTests
end MPC
