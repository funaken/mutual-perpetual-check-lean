import MPC.Geometry.OpenableLineCyclic
import Lean
/-!
# MPC.Tests.OpenableLineCyclic

Concrete checks for the cyclic completion of Proposition 3.3.

- `cyclicBetween` on a five-state period: a non-wrapping interval and a wrapping
  one, with points inside and outside.
- For both first movers, a one-move trace in which a gold dropped between an
  enemy rook and the mover's king blocks the check. It satisfies placement,
  initial opponent safety, and self-safety.
  - Squares the drop does not touch keep their contents (`grid_eq_of_untouched`).
  - The destination holds the mover's gold (`destination_piece_owner`).
  - The mover's king does not step-attack the enemy king before the move
    (`not_stepAttack_of_before`).

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed, and 's verification shows that periodicity is needed. The
board update makes no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Cyclic openable line verification must not import GameSeq"

namespace MPC
namespace OpenableLineCyclicTests

/-! ## Cyclic intervals -/

-- Without wrapping: from 1 to 3.
example : cyclicBetween (1 : Fin 5) 3 2 ∧ ¬ cyclicBetween (1 : Fin 5) 3 4 := by decide

-- Wrapping: from 3 to 1 passes through 4 and 0.
example : cyclicBetween (3 : Fin 5) 1 4 ∧ cyclicBetween (3 : Fin 5) 1 0 ∧
    cyclicBetween (3 : Fin 5) 1 1 ∧ ¬ cyclicBetween (3 : Fin 5) 1 2 := by decide

-- The start always belongs to the interval.
example : cyclicBetween (3 : Fin 5) 1 3 := cyclicBetween_self_left _ _

/-! ## A blocking drop -/

private def col (p : Player) (j : Fin 9) : Pos := (0, if p = .sente then j else 4 - j)
private def far : Pos := (8, 8)

private theorem mem_path (p : Player) : (col p 2).toInt ∈ slidePath (col p 0) (col p 4) := by
  cases p <;> decide

-- The mover's king at the end of the file, an enemy rook checking along it.
private def t0 (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = col p 4 then some ⟨p, .king⟩
        else if q = col p 0 then some ⟨p.opponent, .rook⟩
        else if q = far then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
private def kpB (p : Player) : Fin 2 → Player → Pos := fun _ o => if o = p then col p 4 else far
private def drop (p : Player) : Move := .dropMove .gold (col p 2)
private def tr (p : Player) : MoveTrace := MoveTrace.single (t0 p) (drop p)

-- The drop between the rook and the king blocks the check.
private theorem block_safe (p : Player) :
    ¬ inCheckOriented (applyMove (t0 p) (drop p)).board p (col p 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  by_cases hpos : pos = col p 2
  · subst hpos
    rw [show drop p = .dropMove .gold (col p 2) from rfl, applyMove_dropMove_grid_dst] at hp
    cases hp
    cases p <;> cases ho
  · rw [show drop p = .dropMove .gold (col p 2) from rfl,
      applyMove_dropMove_grid_other _ _ _ _ hpos] at hp
    dsimp only [t0] at hp
    split_ifs at hp with h1 h2 h3 <;> cases hp
    · cases p <;> cases ho
    · subst h2
      have hb := stepAttack_of_attacks_of_blocked _ _ _ _ _ (col p 2) ha (mem_path p)
        (by
          rw [show drop p = .dropMove .gold (col p 2) from rfl, applyMove_dropMove_grid_dst]
          exact Option.some_ne_none _)
      simp [PieceType.stepDirs] at hb
    · subst h3
      rcases ha with hs | ⟨_, hsd, _⟩
      · revert hs
        cases p <;> decide
      · simp [PieceType.slideDirs] at hsd

-- Initially only the mover's king could attack the enemy king, and it is far away.
private theorem start_safe (p : Player) :
    ¬ inCheckOriented (t0 p).board p.opponent far := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [t0] at hp
  split_ifs at hp <;> cases hp
  all_goals first
    | (cases p <;> cases ho; done)
    | (rename_i h; subst h
       rcases ha with hs | ⟨_, hsd, _⟩
       · revert hs
         cases p <;> decide
       · simp [PieceType.slideDirs] at hsd)

-- Both first movers. The untouched rook and king squares keep their contents,
-- the destination holds the mover's gold, and the mover's king does not attack the
-- enemy king by a step before the move.
example (p : Player) :
    ((tr p).states (1 : Fin 2)).board.grid (col p 0) =
      ((tr p).states (0 : Fin 2)).board.grid (col p 0) ∧
    ((tr p).states (1 : Fin 2)).board.grid (col p 4) =
      ((tr p).states (0 : Fin 2)).board.grid (col p 4) ∧
    (∃ P : Piece, ((tr p).states (1 : Fin 2)).board.grid ((tr p).moves (0 : Fin 1)).destination =
      some P ∧ P.owner = p) ∧
    Pos.dirTo (col p 4) ((kpB p) (0 : Fin 2) p.opponent) ∉
      PieceType.king.stepDirs.map (Dir.forPlayer · p) := by
  have ht := MoveTrace.single_followsTransitions (t0 p) (drop p)
  have hs : (tr p).BoardMoveSourcesOwned := by
    intro i src dst pr hm
    have hi := Fin.eq_zero i
    subst i
    cases hm
  have hsafe : (tr p).EveryMoveLeavesOwnKingSafe (kpB p) := by
    intro i
    have hi := Fin.eq_zero i
    subst i
    have h := block_safe p
    cases p
    · exact h
    · exact h
  have h0 : (tr p).InitialOpponentKingSafe (kpB p) := by
    have h := start_safe p
    cases p
    · exact h
    · exact h
  -- The drop touches only its destination.
  have hun : ∀ q : Pos, q ≠ col p 2 → ∀ m : Fin 1, (0 : Fin 2) ≤ m.castSucc →
      m.castSucc < (1 : Fin 2) → ¬ ((tr p).moves m).Touches q := by
    intro q hq m _ _ h
    have hm := Fin.eq_zero m
    subst m
    exact hq h
  refine ⟨(tr p).grid_eq_of_untouched ht (col p 0) (Fin.zero_le _)
      (hun _ (by cases p <;> decide)),
    (tr p).grid_eq_of_untouched ht (col p 4) (Fin.zero_le _) (hun _ (by cases p <;> decide)),
    ?_, ?_⟩
  · obtain ⟨P, hP, hPo⟩ := (tr p).destination_piece_owner ht hs (0 : Fin 1)
    exact ⟨P, hP, hPo⟩
  · have hK : ((tr p).before (0 : Fin 1)).board.grid (col p 4) = some ⟨p, .king⟩ := by
      change (t0 p).board.grid (col p 4) = _
      cases p <;> rfl
    have h := (tr p).not_stepAttack_of_before (kpB p) ht hsafe h0 (0 : Fin 1) (col p 4)
      ⟨p, .king⟩ hK rfl
    cases p
    · exact h
    · exact h

end OpenableLineCyclicTests
end MPC
