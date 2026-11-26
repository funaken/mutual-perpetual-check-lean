import MPC.Invariants.AnglePotential
import Lean
/-!
# MPC.Tests.AnglePotential

Concrete checks for , on one-state traces (no moves), with the first
player's king on `(4, 1)` and the second player's on `(4, 7)`.

- On an empty board the potential is `0`: there is no checker, so `checkerSquare`
  falls back to the first player's king square, whose key is that of the zero
  vector, and there are no non-glaring squares.
- A gold of the first player on `(0, 0)` does not attack the second player's king,
  so its square is among the first player's non-glaring squares and not among the
  second player's.

The step theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Angle potential verification must not import GameSeq"

namespace MPC
namespace AnglePotentialTests

open MoveTrace

/-- The kings: the first player's on `(4, 1)`, the second player's on `(4, 7)`. -/
abbrev kps : Player → Pos := fun p => if p = .sente then (4, 1) else (4, 7)

private def emptyState : BoardState :=
  { board := { grid := fun _ => none, hand := fun _ => ∅ }, turn := .sente }
private def emptyTrace : MoveTrace :=
  { len := 0, states := fun _ => emptyState, moves := Fin.elim0 }

/-! ## The potential of an empty trace -/

-- With no checker, `checkerSquare` falls back to the first player's king, whose key is `0`
-- (the zero vector), and there are no non-glaring squares.
example : emptyTrace.anglePotential (fun _ => kps) .sente 0 = 0 := by
  have hc : emptyTrace.checkerSquare (fun _ => kps) 0 = (4, 1) := by
    unfold MoveTrace.checkerSquare
    rw [dite_eq_right]
    · rfl
    rintro ⟨q, piece, hp, _⟩
    simp [emptyTrace, emptyState] at hp
  have hs : emptyTrace.ownNonGlaringSquares (fun _ => kps) Player.sente.opponent 0 = ∅ := by
    ext q
    rw [MoveTrace.mem_ownNonGlaringSquares]
    simp [emptyTrace, emptyState]
  unfold MoveTrace.anglePotential
  rw [hc, hs, Finset.sum_empty]
  norm_num [angleKey, vecKey, Pos.toInt, Fin.coe_ofNat_eq_mod, kps, Player.opponent]

/-! ## Non-glaring squares of one side -/

/-- The first player's gold on `(0, 0)`, and nothing else. -/
private def goldGrid : Pos → Square :=
  fun q => if q = (0, 0) then some ⟨.sente, .gold⟩ else none

/-- One state with that board. -/
private def goldState : BoardState :=
  { board := { grid := goldGrid, hand := fun _ => ∅ }, turn := .sente }

private def goldTrace : MoveTrace :=
  { len := 0, states := fun _ => goldState, moves := Fin.elim0 }

-- The gold does not attack the second player's king on `(4, 7)`, so it is non-glaring.
example : ((0, 0) : Pos) ∈ goldTrace.ownNonGlaringSquares (fun _ => kps) .sente 0 := by
  rw [MoveTrace.mem_ownNonGlaringSquares]
  refine ⟨⟨⟨.sente, .gold⟩, by simp [goldTrace, goldState, goldGrid], rfl⟩, ?_⟩
  rintro ⟨piece, hp, ha⟩
  simp [goldTrace, goldState, goldGrid] at hp
  subst hp
  simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
    Dir.forPlayer, Pos.dirTo, kps, Player.opponent, Fin.coe_ofNat_eq_mod] at ha

-- It is the first player's, so it is not among the second player's squares.
example : ((0, 0) : Pos) ∉ goldTrace.ownNonGlaringSquares (fun _ => kps) .gote 0 := by
  rw [MoveTrace.mem_ownNonGlaringSquares]
  rintro ⟨⟨X, hX, ho⟩, _⟩
  simp [goldTrace, goldState, goldGrid] at hX
  subst hX
  cases ho

end AnglePotentialTests
end MPC
