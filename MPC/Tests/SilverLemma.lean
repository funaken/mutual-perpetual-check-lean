import MPC.Pieces.SilverLemma
import Lean
/-!
# MPC.Tests.SilverLemma

Concrete checks for , for the first player (`τ = 1`) and `σ = 1`.

- The king's position (`CheckerConstraint`, `king_position_of_silver`):
  - the paper's candidates `(2, 1)` and `(1, 2)` satisfy the constraint at both
    silver moves;
  - `(1, 1)`, and `(1, -1)` through an enemy knight on `(0, 1)` (the paper's
    footnote 7), satisfy it too, so the premise that the kings are not adjacent
    is needed;
  - `(2, -1)` fails it at the move to `(0, 1)`: the line from `(2, -1)` to `(0, 1)`
    passes the silver's own square `(1, 0)`.
- Kinds: a lance sliding forward along a file and a bishop sliding diagonally are
  not rooks or dragons, so both premises of `rookDragon_of_slideDir` are needed.
  A rook attacking `(4, 4)` from `(4, 0)` on an empty board slides along `(0, 1)`
  (`slideDir_of_attack_not_step`).
- `false_of_three_rookDragon`: a one-state trace with three rooks violates
  `PieceCountsAtMostTwo`.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Silver lemma verification must not import GameSeq"

namespace MPC
namespace SilverLemmaTests

/-! ## The king's position -/

-- The paper's two candidates satisfy the constraint at both moves.
example : CheckerConstraint 1 (0, 1) (1, 0) (2, 1) ∧ CheckerConstraint 1 (1, 0) (0, 1) (2, 1) ∧
    CheckerConstraint 1 (0, 1) (1, 0) (1, 2) ∧ CheckerConstraint 1 (1, 0) (0, 1) (1, 2) := by
  refine ⟨Or.inl ⟨(1, 0), by decide, 2, by norm_num, by decide, fun _ => by decide⟩,
    Or.inl ⟨(1, 1), by decide, 1, le_refl _, by decide, fun h => absurd h (by norm_num)⟩,
    Or.inl ⟨(1, 1), by decide, 1, le_refl _, by decide, fun h => absurd h (by norm_num)⟩,
    Or.inl ⟨(0, 1), by decide, 2, by norm_num, by decide, fun _ => by decide⟩⟩

-- Squares next to the enemy king pass too; `(1, -1)` through an enemy knight.
example : CheckerConstraint 1 (0, 1) (1, 0) (1, 1) ∧ CheckerConstraint 1 (1, 0) (0, 1) (1, 1) ∧
    CheckerConstraint 1 (0, 1) (1, 0) (1, -1) ∧ CheckerConstraint 1 (1, 0) (0, 1) (1, -1) := by
  refine ⟨Or.inl ⟨(1, 0), by decide, 1, le_refl _, by decide, fun h => absurd h (by norm_num)⟩,
    Or.inl ⟨(0, 1), by decide, 1, le_refl _, by decide, fun h => absurd h (by norm_num)⟩,
    Or.inr (by decide),
    Or.inl ⟨(0, -1), by decide, 1, le_refl _, by decide, fun h => absurd h (by norm_num)⟩⟩

-- `(2, -1)` sees `(0, 1)` only through the silver's own square `(1, 0)`.
example : ¬ CheckerConstraint 1 (0, 1) (1, 0) (2, -1) := by
  rintro (⟨sd, hsd, c, hc, hl, hblk⟩ | ⟨h1, _⟩)
  · simp only [PieceType.stepDirs, List.mem_cons, List.not_mem_nil,
      or_false] at hsd
    rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prod.mk.injEq, ne_eq] at hl hblk <;> omega
  · dsimp only at h1
    omega

/-! ## Kinds -/

-- A forward lance slide and a diagonal bishop slide are not rooks or dragons.
example : ((0, 1) : Dir) ∈ PieceType.lance.slideDirs.map (Dir.forPlayer · .sente) ∧
    ((1, 1) : Dir) ∈ PieceType.bishop.slideDirs.map (Dir.forPlayer · .sente) ∧
    ¬ (PieceType.lance = .rook ∨ PieceType.lance = .dragon) ∧
    ¬ (PieceType.bishop = .rook ∨ PieceType.bishop = .dragon) := by decide

private def emptyBoard : Board := { grid := fun _ => none, hand := fun _ => ∅ }

-- A rook on `(4, 0)` attacking `(4, 4)` slides along `(0, 1)`.
example : ((0, 1) : Dir) ∈ PieceType.rook.slideDirs.map (Dir.forPlayer · .sente) := by
  have h := slideDir_of_attack_not_step emptyBoard .sente .rook ((4, 0) : Pos) ((4, 4) : Pos)
    (Or.inr ⟨(0, 1), by decide, by decide, 4, by decide, by decide, by decide,
      fun _ _ _ _ => rfl⟩)
    (by simp [PieceType.stepDirs]) (d := (0, -1)) (n := 4) (by unfold OnRay; decide)
  simpa using h

/-! ## Three rooks -/

private def threeRooks : BoardState :=
  { board :=
    { grid := fun q =>
        if q = ((0, 0) : Pos) ∨ q = ((1, 0) : Pos) ∨ q = ((2, 0) : Pos) then
          some ⟨.sente, .rook⟩ else none
      hand := fun _ => ∅ }
    turn := .sente }

private def oneState : MoveTrace := { len := 0, states := fun _ => threeRooks, moves := Fin.elim0 }

example : ¬ oneState.PieceCountsAtMostTwo := by
  intro hcount
  have hmem : ∀ q : Pos, (q = ((0, 0) : Pos) ∨ q = ((1, 0) : Pos) ∨ q = ((2, 0) : Pos)) →
      q ∈ oneState.rookDragonSquares 0 := fun q hq =>
    oneState.mem_rookDragonSquares_of 0 q ⟨.sente, .rook⟩
      (by change (if _ then _ else _) = _; rw [ite_eq_left hq]) (Or.inl rfl)
  exact oneState.false_of_three_rookDragon hcount 0 (0, 0) (1, 0) (2, 0) (by decide) (by decide)
    (by decide) (hmem _ (Or.inl rfl)) (hmem _ (Or.inr (Or.inl rfl)))
    (hmem _ (Or.inr (Or.inr rfl)))

end SilverLemmaTests
end MPC
