import MPC.Invariants.CheckerAngle
import Lean
/-!
# MPC.Tests.CheckerAngle

Concrete checks for , with the enemy king `K` on `(4, 1)` and the own king
`L` on `(4, 7)` as in .

- `angleKey_eq_of_onRay`: `(2, 3)` and `(1, 4)` are two and three steps of
  `(-1, 1)` from `K`, so they share a key. In the paper's terms, an enemy piece that
  interposes on `(2, 3)` against a checker on `(1, 4)` makes the checker's angle.
- `angleKey_lt_of_onRay`: `(2, 5)` and `(1, 4)` are two and three steps of
  `(-1, -1)` from `L`, so the interposition on `(2, 5)` has the smaller key.
- `checkerSquare` falls back to the first player's king square when no square
  checks: on an empty one-state trace it is that square.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Checker angle verification must not import GameSeq"

namespace MPC
namespace CheckerAngleTests

/-- The enemy king. -/
abbrev K : Pos := (4, 1)
/-- The own king. -/
abbrev L : Pos := (4, 7)

/-! ## One half-line from a king -/

example : angleKey K L (2, 3) = angleKey K L (1, 4) :=
  angleKey_eq_of_onRay (e := (-1, 1)) (a := 2) (b := 3)
    ⟨by decide, by norm_num, by decide⟩ ⟨by decide, by norm_num, by decide⟩

/-! ## An interposition toward the own king -/

example : angleKey K L (2, 5) < angleKey K L (1, 4) :=
  angleKey_lt_of_onRay (e := (-1, -1)) (n := 3) (c := 2)
    ⟨by decide, by norm_num, by decide⟩ ⟨by decide, by norm_num, by decide⟩ (by norm_num)
    (by decide)

/-! ## The fallback of `checkerSquare` -/

private def emptyState : BoardState :=
  { board := { grid := fun _ => none, hand := fun _ => ∅ }, turn := .sente }

private def emptyTrace : MoveTrace :=
  { len := 0, states := fun _ => emptyState, moves := Fin.elim0 }

example : emptyTrace.checkerSquare (fun _ _ => K) 0 = K := by
  unfold MoveTrace.checkerSquare
  rw [dite_eq_right]
  rintro ⟨q, piece, hp, _⟩
  simp [emptyTrace, emptyState] at hp

end CheckerAngleTests
end MPC
