import MPC.Legacy.CheckCompatibility
import MPC.Geometry.OpenableLine
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.OpenableLine

The periodicity-free parts of Proposition 3.3 and Corollary 3.4, for both first
movers.

- A one-move trace: a gold steps onto the file between the mover's rook and the
  enemy king. The rook glares through that occupied square (which a move
  touches, so it is not immovable). The gold does not glare, so glaring
  destinations are trivially direct checks, and the king positions are
  constant. The interval theorem then keeps the rook on its square throughout,
  and the blocking lemma shows that the rook no longer attacks the king.
- A one-move trace: an enemy rook checks the mover's king along a file. A gold
  dropped between them lands on the checker's line, by Corollary 3.4's second
  half. A gold dropped elsewhere breaks self-safety, which the same theorem
  detects.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed. That periodicity is needed is shown in 's verification. Board
updates make no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Openable line verification must not import GameSeq"

namespace MPC
namespace OpenableLineTests

private def col (p : Player) (j : Fin 9) : Pos := (0, if p = .sente then j else 4 - j)
private def far : Pos := (8, 8)

private theorem col_clear (b : Board) (p : Player) :
    pathClear b (col p 0) (col p 4) ↔
      b.grid (col p 1) = none ∧ b.grid (col p 2) = none ∧ b.grid (col p 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (col p 0) (col p 4)
    (0, if p = .sente then 1 else -1) 4 (by cases p <;> decide) (by decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h3 := hc.mp h 3 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    cases p <;> exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j <;> cases p <;> assumption

-- A rook of either owner attacks along the file once it is clear.
private theorem col_attack (b : Board) (p o : Player) (hc : pathClear b (col p 0) (col p 4)) :
    attacksOriented b o .rook (col p 0) (col p 4) := by
  refine Or.inr ⟨(0, if p = .sente then 1 else -1), ?_, ?_, 4, by decide, ?_, ?_, hc⟩ <;>
    cases p <;> cases o <;> decide

private theorem mem_path (p : Player) : (col p 2).toInt ∈ slidePath (col p 0) (col p 4) := by
  cases p <;> decide

/-! ## The interval theorem: a rook keeps glaring through an occupied square -/

-- The mover's rook on the file, a gold beside the file, the enemy king at its end.
private def s0 (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = col p 0 then some ⟨p, .rook⟩
        else if q = (1, 2) then some ⟨p, .gold⟩
        else if q = col p 4 then some ⟨p.opponent, .king⟩
        else if q = far then some ⟨p, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
-- The gold steps onto the file.
private def block (p : Player) : Move := .boardMove (1, 2) (col p 2) false
private def trA (p : Player) : MoveTrace := MoveTrace.single (s0 p) (block p)
private def kpA (p : Player) : Fin 2 → Player → Pos := fun _ o => if o = p then far else col p 4

private theorem s1_grid (p : Player) (q : Pos) :
    (applyMove (s0 p) (block p)).board.grid q =
      if q = col p 2 then some ⟨p, .gold⟩
      else if q = (1, 2) then none else (s0 p).board.grid q := by
  unfold block
  have hd : ((1, 2) : Pos) ≠ col p 2 := by cases p <;> decide
  by_cases hq : q = col p 2
  · subst q
    rw [ite_eq_left rfl, applyMove_boardMove_grid_dst]
    cases p <;> rfl
  · by_cases hs : q = (1, 2)
    · subst q
      rw [ite_eq_right hq, ite_eq_left rfl]
      exact applyMove_boardMove_grid_src (s0 p) (1, 2) (col p 2) false hd
    · rw [ite_eq_right hq, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (s0 p) (1, 2) (col p 2) false q hs hq

private theorem rook_after (p : Player) :
    ((trA p).states (1 : Fin 2)).board.grid (col p 0) = some ⟨p, .rook⟩ := by
  change (applyMove (s0 p) (block p)).board.grid (col p 0) = _
  rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
  cases p <;> rfl

private theorem gold_after (p : Player) :
    ((trA p).states (1 : Fin 2)).board.grid (col p 2) = some ⟨p, .gold⟩ := by
  change (applyMove (s0 p) (block p)).board.grid (col p 2) = _
  rw [s1_grid, ite_eq_left rfl]

-- On the stripped board the file is clear: none of its squares starts occupied,
-- so none is immovable.
private theorem stripped_clear (p : Player) (j : Fin 9) (hj : col p j ≠ col p 0)
    (h0 : (s0 p).board.grid (col p j) = none) :
    ((trA p).strippedBoard (1 : Fin 2) (col p 0)).grid (col p j) = none := by
  simp only [MoveTrace.strippedBoard]
  rw [ite_eq_right]
  rintro (h | h)
  · exact hj h
  · exact h.1 h0

private theorem rook_glares (p : Player) :
    (trA p).GlaresAtEnemyKing (kpA p) (1 : Fin 2) (col p 0) := by
  refine ⟨⟨p, .rook⟩, rook_after p, ?_⟩
  have h := col_attack ((trA p).strippedBoard (1 : Fin 2) (col p 0)) p p
    ((col_clear _ p).mpr ⟨stripped_clear p 1 (by cases p <;> decide) (by cases p <;> rfl),
      stripped_clear p 2 (by cases p <;> decide) (by cases p <;> rfl),
      stripped_clear p 3 (by cases p <;> decide) (by cases p <;> rfl)⟩)
  cases p
  · exact h
  · exact h

-- The gold, two squares from the enemy king, does not glare.
private theorem gold_not_glares (p : Player) :
    ¬ (trA p).GlaresAtEnemyKing (kpA p) (1 : Fin 2) (col p 2) := by
  rintro ⟨piece, hp, ha⟩
  rw [gold_after] at hp
  cases hp
  rcases ha with hs | ⟨_, hsd, _⟩
  · revert hs
    cases p <;> decide
  · simp [PieceType.slideDirs] at hsd

-- Both first movers. With glaring destinations trivially direct checks and
-- constant king positions, the rook glaring through the occupied square stays on
-- its square in every state; and the occupied square blocks its attack.
example (p : Player) :
    (∀ k : Fin 2, ((trA p).states k).board.grid (col p 0) = some ⟨p, .rook⟩) ∧
    ¬ attacksOriented ((trA p).states (1 : Fin 2)).board p .rook (col p 0) (col p 4) := by
  have ht := MoveTrace.single_followsTransitions (s0 p) (block p)
  have hd : (trA p).BoardMoveEndpointsDistinct := by
    intro i src dst pr hm
    have hi := Fin.eq_zero i
    subst i
    change Move.boardMove (1, 2) (col p 2) false = .boardMove src dst pr at hm
    cases hm
    cases p <;> decide
  have hgd : (trA p).GlaringDestinationsCheck (kpA p) := by
    intro i hg
    have hi := Fin.eq_zero i
    subst i
    exact absurd hg (gold_not_glares p)
  have hA : (col p 2).toInt ∈
      slidePath (col p 0) (kpA p 0 (⟨p, .rook⟩ : Piece).owner.opponent) := by
    have h := mem_path p
    cases p
    · exact h
    · exact h
  have hstep : Pos.dirTo (col p 0) (kpA p 0 (⟨p, .rook⟩ : Piece).owner.opponent) ∉
      PieceType.rook.stepDirs.map (Dir.forPlayer · p) := by
    simp [PieceType.stepDirs]
  have hocc : ∀ k : Fin 2, (0 : Fin 2) < k → k ≤ (1 : Fin 2) →
      ((trA p).states k).board.grid (col p 2) ≠ none := by
    intro k hk _
    have hk1 : k = 1 := by
      rw [Fin.lt_def] at hk
      exact Fin.ext (by have := k.isLt; simp at hk ⊢; omega)
    subst hk1
    rw [gold_after]
    exact Option.some_ne_none _
  refine ⟨fun k => (trA p).grid_eq_of_glares_through_occupied (kpA p) ht hd (fun _ => rfl) hgd
    (a := 0) (b := 1) (col p 0) (col p 2) ⟨p, .rook⟩ (rook_after p) (rook_glares p) hA hstep
    hocc k (Fin.zero_le k) (Fin.le_last k), ?_⟩
  intro ha
  have h := stepAttack_of_attacks_of_blocked _ _ _ _ _ (col p 2) ha (mem_path p)
    (by rw [gold_after]; exact Option.some_ne_none _)
  simp [PieceType.stepDirs] at h

/-! ## Corollary 3.4's second half: a check is resolved on the checker's line -/

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
private def drop (dst : Pos) : Move := .dropMove .gold dst
private def trB (p : Player) (dst : Pos) : MoveTrace := MoveTrace.single (t0 p) (drop dst)

private theorem rook_checks (p : Player) :
    attacksOriented (t0 p).board p.opponent .rook (col p 0) (col p 4) :=
  col_attack _ p p.opponent ((col_clear _ p).mpr
    ⟨by cases p <;> rfl, by cases p <;> rfl, by cases p <;> rfl⟩)

-- The drop between the rook and the king blocks the check.
private theorem block_safe (p : Player) :
    ¬ inCheckOriented (applyMove (t0 p) (drop (col p 2))).board p (col p 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  by_cases hpos : pos = col p 2
  · subst hpos
    rw [show drop (col p 2) = .dropMove .gold (col p 2) from rfl, applyMove_dropMove_grid_dst] at hp
    cases hp
    cases p <;> cases ho
  · rw [show drop (col p 2) = .dropMove .gold (col p 2) from rfl,
      applyMove_dropMove_grid_other _ _ _ _ hpos] at hp
    dsimp only [t0] at hp
    split_ifs at hp with h1 h2 h3 <;> cases hp
    · cases p <;> cases ho
    · subst h2
      have hb := stepAttack_of_attacks_of_blocked _ _ _ _ _ (col p 2) ha (mem_path p)
        (by
          rw [show drop (col p 2) = .dropMove .gold (col p 2) from rfl,
            applyMove_dropMove_grid_dst]
          exact Option.some_ne_none _)
      simp [PieceType.stepDirs] at hb
    · subst h3
      rcases ha with hs | ⟨_, hsd, _⟩
      · revert hs
        cases p <;> decide
      · simp [PieceType.slideDirs] at hsd

-- Both first movers. The blocking drop satisfies self-safety, and Corollary
-- 3.4's second half places it on the checking rook's line.
example (p : Player) :
    (col p 2).toInt ∈ slidePath (col p 0) (col p 4) ∧
      Pos.dirTo (col p 0) (col p 4) ∉
        PieceType.rook.stepDirs.map (Dir.forPlayer · p.opponent) := by
  have ht := MoveTrace.single_followsTransitions (t0 p) (drop (col p 2))
  have hs : (trB p (col p 2)).BoardMoveSourcesOwned := by
    intro i src dst pr hm
    have hi := Fin.eq_zero i
    subst i
    cases hm
  have hsafe : (trB p (col p 2)).EveryMoveLeavesOwnKingSafe (kpB p) := by
    intro i
    have hi := Fin.eq_zero i
    subst i
    have h := block_safe p
    cases p
    · exact h
    · exact h
  have hX : ((trB p (col p 2)).before (0 : Fin 1)).board.grid (col p 0) =
      some ⟨p.opponent, .rook⟩ := by
    change (t0 p).board.grid (col p 0) = _
    cases p <;> rfl
  have hatk : attacksOriented ((trB p (col p 2)).before (0 : Fin 1)).board p.opponent .rook
      (col p 0) ((kpB p) (0 : Fin 1).castSucc ((trB p (col p 2)).before (0 : Fin 1)).turn) := by
    have h := rook_checks p
    cases p
    · exact h
    · exact h
  have h := (trB p (col p 2)).destination_on_checker_line (kpB p) ht hs hsafe (0 : Fin 1) rfl
    (col p 0) ⟨p.opponent, .rook⟩ hX (by cases p <;> rfl) hatk
  rcases h with h | h
  · exact absurd h (by cases p <;> decide)
  · cases p
    · exact h
    · exact h

-- Both first movers. A gold dropped off the line leaves the check in place:
-- Corollary 3.4's second half shows such a trace cannot be self-safe.
private def off : Pos := (5, 5)

example (p : Player) : ¬ (trB p off).EveryMoveLeavesOwnKingSafe (kpB p) := by
  intro hsafe
  have ht := MoveTrace.single_followsTransitions (t0 p) (drop off)
  have hs : (trB p off).BoardMoveSourcesOwned := by
    intro i src dst pr hm
    have hi := Fin.eq_zero i
    subst i
    cases hm
  have hX : ((trB p off).before (0 : Fin 1)).board.grid (col p 0) =
      some ⟨p.opponent, .rook⟩ := by
    change (t0 p).board.grid (col p 0) = _
    cases p <;> rfl
  have hatk : attacksOriented ((trB p off).before (0 : Fin 1)).board p.opponent .rook
      (col p 0) ((kpB p) (0 : Fin 1).castSucc ((trB p off).before (0 : Fin 1)).turn) := by
    have h := rook_checks p
    cases p
    · exact h
    · exact h
  rcases (trB p off).destination_on_checker_line (kpB p) ht hs hsafe (0 : Fin 1) rfl
    (col p 0) ⟨p.opponent, .rook⟩ hX (by cases p <;> rfl) hatk with h | ⟨h, _⟩
  · change off = col p 0 at h
    exact absurd h (by cases p <;> decide)
  · revert h
    cases p <;> decide

end OpenableLineTests
end MPC
