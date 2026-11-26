import MPC.Legacy.CheckCompatibility
import MPC.Pieces.RookDragonLemma
import Lean
/-!
# MPC.Tests.RookDragonLemma

Concrete checks for .

- Kinds: rooks and dragons slide along every rank and file direction for both
  players (`orth_mem_rookDragon_slideDirs`). A diagonal slider is a bishop or a
  horse (`bishopHorse_of_slideDir`), and the diagonal premise is needed: a rook
  slides along a file.
- `normalize_mul_of_king_step` on concrete multiples.
- The geometric step of the central lemma, on a concrete board. A rook on `(4, 0)`
  attacks the king on `(4, 4)` through a rook on `(4, 2)`, on a board holding only
  the far rook and the king. The rook on `(4, 2)` then attacks the king too, on a
  board holding only it and the king. So an openable rook cannot stand on a file
  or rank behind which another piece glares.
- `false_of_three_bishopHorse`: a one-state trace with three bishops violates
  `PieceCountsAtMostTwo`.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Rook/dragon lemma verification must not import GameSeq"

namespace MPC
namespace RookDragonLemmaTests

/-! ## Kinds and directions -/

example : ((0, -1) : Dir) ∈ PieceType.rook.slideDirs.map (Dir.forPlayer · .gote) ∧
    ((1, 0) : Dir) ∈ PieceType.dragon.slideDirs.map (Dir.forPlayer · .sente) :=
  ⟨orth_mem_rookDragon_slideDirs _ _ _ (Or.inl rfl) (by decide) (Or.inl rfl),
    orth_mem_rookDragon_slideDirs _ _ _ (Or.inr rfl) (by decide) (Or.inr rfl)⟩

-- A diagonal slider is a bishop or a horse; a file slider need not be.
example : (PieceType.horse = .bishop ∨ PieceType.horse = .horse) ∧
    ((0, 1) : Dir) ∈ PieceType.rook.slideDirs.map (Dir.forPlayer · .sente) ∧
    ¬ (PieceType.rook = .bishop ∨ PieceType.rook = .horse) :=
  ⟨bishopHorse_of_slideDir .horse .sente (1, -1) (by decide) (by decide) (by decide),
    by decide, by decide⟩

example : Dir.normalize (3 * 1, 3 * -1) = (1, -1) ∧ Dir.normalize (5 * 0, 5 * 1) = (0, 1) :=
  ⟨normalize_mul_of_king_step (d := (1, -1)) (b := 3) (by decide) (by norm_num),
    normalize_mul_of_king_step (d := (0, 1)) (b := 5) (by decide) (by norm_num)⟩

/-! ## A rook behind a rook on a file -/

private def K : Pos := (4, 4)

private theorem toInt_toPos (q : ℤ × ℤ) (h : onBoard q) : (toPos q h).toInt = q := by
  obtain ⟨h1, _, h2, _⟩ := h
  ext
  · simp [toPos, Pos.toInt]; omega
  · simp [toPos, Pos.toInt]; omega

-- Only the far rook and the king.
private def farBoard : Board :=
  { grid := fun q => if q = ((4, 0) : Pos) then some ⟨.sente, .rook⟩
      else if q = K then some ⟨.gote, .king⟩ else none
    hand := fun _ => ∅ }

-- Only the near rook and the king.
private def nearBoard : Board :=
  { grid := fun q => if q = ((4, 2) : Pos) then some ⟨.sente, .rook⟩
      else if q = K then some ⟨.gote, .king⟩ else none
    hand := fun _ => ∅ }

private theorem farBoard_empty (q : Pos) (h1 : q ≠ ((4, 0) : Pos)) (h2 : q ≠ K) :
    farBoard.grid q = none := by
  simp only [farBoard, ite_eq_right h1, ite_eq_right h2]

private theorem nearBoard_empty (q : Pos) (h1 : q ≠ ((4, 2) : Pos)) (h2 : q ≠ K) :
    nearBoard.grid q = none := by
  simp only [nearBoard, ite_eq_right h1, ite_eq_right h2]

-- The far rook attacks the king through `(4, 2)`, and so does the near rook.
example : ((4 : ℤ), (2 : ℤ)) ∈ slidePath ((4, 0) : Pos) K ∧
    attacksOriented farBoard .sente .rook ((4, 0) : Pos) K ∧
    attacksOriented nearBoard .sente .rook ((4, 2) : Pos) K := by
  refine ⟨by unfold K; decide, Or.inr ⟨(0, 1), by decide, by unfold K; decide, 4, by decide,
    by unfold K; decide, by unfold K; decide, ?_⟩, Or.inr ⟨(0, 1), by decide, by unfold K; decide,
    2, by decide, by unfold K; decide, by unfold K; decide, ?_⟩⟩
  · intro q hq _ h
    apply farBoard_empty
    · intro he
      have he' := congrArg Pos.toInt he
      rw [toInt_toPos] at he'
      rw [he'] at hq
      revert hq
      unfold K
      decide
    · intro he
      have he' := congrArg Pos.toInt he
      rw [toInt_toPos] at he'
      rw [he'] at hq
      revert hq
      unfold K
      decide
  · intro q hq _ h
    apply nearBoard_empty
    · intro he
      have he' := congrArg Pos.toInt he
      rw [toInt_toPos] at he'
      rw [he'] at hq
      revert hq
      unfold K
      decide
    · intro he
      have he' := congrArg Pos.toInt he
      rw [toInt_toPos] at he'
      rw [he'] at hq
      revert hq
      unfold K
      decide

/-! ## Three bishops -/

private def threeBishops : BoardState :=
  { board :=
    { grid := fun q =>
        if q = ((0, 0) : Pos) ∨ q = ((1, 0) : Pos) ∨ q = ((2, 0) : Pos) then
          some ⟨.gote, .bishop⟩ else none
      hand := fun _ => ∅ }
    turn := .sente }

private def oneState : MoveTrace :=
  { len := 0, states := fun _ => threeBishops, moves := Fin.elim0 }

example : ¬ oneState.PieceCountsAtMostTwo := by
  intro hcount
  have hmem : ∀ q : Pos, (q = ((0, 0) : Pos) ∨ q = ((1, 0) : Pos) ∨ q = ((2, 0) : Pos)) →
      q ∈ oneState.bishopHorseSquares 0 := fun q hq =>
    oneState.mem_bishopHorseSquares_of 0 q ⟨.gote, .bishop⟩
      (by change (if _ then _ else _) = _; rw [ite_eq_left hq]) (Or.inl rfl)
  exact oneState.false_of_three_bishopHorse hcount 0 (0, 0) (1, 0) (2, 0) (by decide) (by decide)
    (by decide) (hmem _ (Or.inl rfl)) (hmem _ (Or.inr (Or.inl rfl)))
    (hmem _ (Or.inr (Or.inr rfl)))

end RookDragonLemmaTests
end MPC
