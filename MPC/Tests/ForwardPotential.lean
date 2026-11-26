import MPC.Invariants.ForwardPotential
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.ForwardPotential

Concrete checks for .

- Forward ranks, and the strict forward step of a knight, a lance, and a pawn for
  both owners (`forwardRank_lt_of_canMoveToOriented`).
- A gold and a tokin can step backwards, so the lemma needs its kind restriction.
  The potential argument also needs : a pawn that promoted could retreat.
- For both first movers, a one-move trace in which a knight blocking its own rook
  jumps forward off the file, and the rook gives a discovered check. It satisfies
  every premise of the periodic theorems except periodicity, the knight does not
  glare, and its owner's forward rank rises. So
  `not_nonGlaring_forward_move_of_periodic` fails without periodicity.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed. The board update makes no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Forward potential verification must not import GameSeq"

namespace MPC
namespace ForwardPotentialTests

/-! ## Forward moves -/

private def emptyBoard : Board := { grid := fun _ => none, hand := fun _ => ∅ }

example : forwardRank .sente ((4, 6) : Pos) = 6 ∧ forwardRank .gote ((4, 6) : Pos) = 2 :=
  ⟨rfl, rfl⟩

-- A sente knight jump, a gote pawn step, and a gote lance slide all go forward.
example : forwardRank .sente ((3, 2) : Pos) < forwardRank .sente ((4, 4) : Pos) ∧
    forwardRank .gote ((4, 6) : Pos) < forwardRank .gote ((4, 5) : Pos) ∧
    forwardRank .gote ((4, 6) : Pos) < forwardRank .gote ((4, 2) : Pos) :=
  ⟨forwardRank_lt_of_canMoveToOriented emptyBoard .sente .knight _ _ (Or.inl rfl)
      (Or.inl (by decide)),
    forwardRank_lt_of_canMoveToOriented emptyBoard .gote .pawn _ _ (Or.inr (Or.inr rfl))
      (Or.inl (by decide)),
    forwardRank_lt_of_canMoveToOriented emptyBoard .gote .lance _ _ (Or.inr (Or.inl rfl))
      (Or.inr ⟨(0, -1), by decide, by decide, 4, by decide, by decide, by decide,
        fun _ _ _ _ => rfl⟩)⟩

-- A gold and a tokin can step backwards: the kind restriction is needed.
example : canMoveToOriented emptyBoard .sente .gold ((4, 4) : Pos) ((4, 3) : Pos) ∧
    canMoveToOriented emptyBoard .sente .tokin ((4, 4) : Pos) ((4, 3) : Pos) ∧
    forwardRank .sente ((4, 3) : Pos) < forwardRank .sente ((4, 4) : Pos) :=
  ⟨Or.inl (by decide), Or.inl (by decide), by decide⟩

/-! ## A knight jumps off its rook's file -/

-- Rank `j` counted from the mover's rook toward the enemy king.
private def y (p : Player) (j : Fin 9) : Fin 9 := if p = .sente then 4 + j else 4 - j
private def rookSq (p : Player) : Pos := (0, y p 0)
private def knightSq (p : Player) : Pos := (0, y p 2)
private def enemySq (p : Player) : Pos := (0, y p 4)
private def dstSq (p : Player) : Pos := (1, y p 4)
private def kingSq (p : Player) : Pos := (8, y p 0)

private def s0 (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = rookSq p then some ⟨p, .rook⟩
        else if q = knightSq p then some ⟨p, .knight⟩
        else if q = kingSq p then some ⟨p, .king⟩
        else if q = enemySq p then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
-- The knight jumps forward off the file.
private def jump (p : Player) : Move := .boardMove (knightSq p) (dstSq p) false
private def tr (p : Player) : MoveTrace := MoveTrace.single (s0 p) (jump p)
private def kpc (p : Player) : Fin 2 → Player → Pos :=
  fun _ o => if o = p then kingSq p else enemySq p

private theorem s1_grid (p : Player) (q : Pos) :
    (applyMove (s0 p) (jump p)).board.grid q =
      if q = dstSq p then some ⟨p, .knight⟩
      else if q = knightSq p then none else (s0 p).board.grid q := by
  unfold jump
  have hd : knightSq p ≠ dstSq p := by cases p <;> decide
  by_cases hq : q = dstSq p
  · subst q
    rw [ite_eq_left rfl, applyMove_boardMove_grid_dst]
    cases p <;> rfl
  · by_cases hs : q = knightSq p
    · subst q
      rw [ite_eq_right hq, ite_eq_left rfl]
      exact applyMove_boardMove_grid_src (s0 p) (knightSq p) (dstSq p) false hd
    · rw [ite_eq_right hq, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (s0 p) (knightSq p) (dstSq p) false q hs hq

private theorem file_clear (b : Board) (p : Player) :
    pathClear b (rookSq p) (enemySq p) ↔
      b.grid (0, y p 1) = none ∧ b.grid (knightSq p) = none ∧ b.grid (0, y p 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (rookSq p) (enemySq p)
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

private theorem file_attack (b : Board) (p : Player) :
    attacksOriented b p .rook (rookSq p) (enemySq p) ↔ pathClear b (rookSq p) (enemySq p) := by
  constructor
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · simp [PieceType.stepDirs] at hs
    · exact hc
  · intro hc
    refine Or.inr ⟨(0, if p = .sente then 1 else -1), ?_, ?_, 4, by decide, ?_, ?_, hc⟩ <;>
      cases p <;> decide

private theorem opponent_ne (p : Player) : p.opponent ≠ p := by
  cases p <;> decide

-- Placement from the two king squares and the absence of other kings.
private theorem placed_of (p : Player) (b : Board)
    (hk : b.grid (kingSq p) = some ⟨p, .king⟩)
    (he : b.grid (enemySq p) = some ⟨p.opponent, .king⟩)
    (hother : ∀ q o, b.grid q = some ⟨o, .king⟩ → q = kingSq p ∨ q = enemySq p) :
    KingsWellPlaced b (fun o => if o = p then kingSq p else enemySq p) := by
  intro o q
  constructor
  · intro h
    rcases hother q o h with rfl | rfl
    · rw [hk] at h
      cases h
      exact (ite_eq_left rfl).symm
    · rw [he] at h
      cases h
      exact (ite_eq_right (opponent_ne p)).symm
  · intro h
    subst h
    by_cases ho : o = p
    · subst ho
      dsimp only
      rw [ite_eq_left rfl]
      exact hk
    · have ho' : o = p.opponent := by cases o <;> cases p <;> first | rfl | exact absurd rfl ho
      subst ho'
      dsimp only
      rw [ite_eq_right ho]
      exact he

private theorem placed0 (p : Player) :
    KingsWellPlaced (s0 p).board (fun o => if o = p then kingSq p else enemySq p) := by
  refine placed_of p _ (by cases p <;> rfl) (by cases p <;> rfl) ?_
  intro q o h
  dsimp only [s0] at h
  split_ifs at h
  all_goals first
    | exact Or.inl ‹_›
    | exact Or.inr ‹_›
    | cases h

private theorem placed1 (p : Player) :
    KingsWellPlaced (applyMove (s0 p) (jump p)).board
      (fun o => if o = p then kingSq p else enemySq p) := by
  refine placed_of p _ ?_ ?_ ?_
  · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · intro q o h
    rw [s1_grid] at h
    dsimp only [s0] at h
    split_ifs at h
    all_goals first
      | exact Or.inl ‹_›
      | exact Or.inr ‹_›
      | cases h

-- Initially the knight blocks the rook, and the knight and the king are too far.
private theorem start_safe (p : Player) :
    ¬ inCheckOriented (s0 p).board p.opponent (enemySq p) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [s0] at hp
  split_ifs at hp with h1 h2 h3 h4 <;> cases hp
  · subst h1
    have h := ((file_clear _ p).mp ((file_attack _ p).mp ha)).2.1
    have hs : (s0 p).board.grid (knightSq p) = some ⟨p, .knight⟩ := by cases p <;> rfl
    rw [hs] at h
    cases h
  · subst h2
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd
  · subst h3
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd
  · cases p <;> cases ho

-- After the move only the enemy king opposes the mover's king, far away.
private theorem after_safe (p : Player) :
    ¬ inCheckOriented (applyMove (s0 p) (jump p)).board p (kingSq p) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [s1_grid] at hp
  dsimp only [s0] at hp
  split_ifs at hp <;> cases hp
  all_goals first
    | (cases p <;> cases ho; done)
    | (rename_i h; subst h
       rcases ha with hs | ⟨_, hsd, _⟩
       · revert hs
         cases p <;> decide
       · simp [PieceType.slideDirs] at hsd)

-- The knight has left the file, so the rook checks the enemy king.
private theorem rook_check (p : Player) :
    inCheckOriented (applyMove (s0 p) (jump p)).board p.opponent (enemySq p) := by
  refine ⟨rookSq p, ⟨p, .rook⟩, ?_, by cases p <;> rfl, ?_⟩
  · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · refine (file_attack _ p).mpr ((file_clear _ p).mpr ⟨?_, ?_, ?_⟩)
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_left rfl]
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl

private def premises (p : Player) : Prop :=
  (tr p).FollowsTransitions ∧ (tr p).BoardMoveSourcesOwned ∧
    (tr p).KingsWellPlaced (kpc p) ∧ (tr p).EveryMoveLeavesOwnKingSafe (kpc p) ∧
    (tr p).InitialOpponentKingSafe (kpc p) ∧ (tr p).EveryMoveChecksOpponent (kpc p) ∧
    (tr p).BoardMovesFollowCanMoveToOriented

-- Every premise of the periodic theorems except periodicity.
private theorem premises_hold (p : Player) : premises p := by
  refine ⟨MoveTrace.single_followsTransitions _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (knightSq p) (dstSq p) false = .boardMove src dst pr at hm
    cases hm
    exact ⟨⟨p, .knight⟩, by cases p <;> rfl, rfl⟩
  · intro k
    match k with
    | ⟨0, _⟩ => exact placed0 p
    | ⟨1, _⟩ => exact placed1 p
  · intro i; have hi := Fin.eq_zero i; subst i
    have h := after_safe p
    cases p
    · exact h
    · exact h
  · have h := start_safe p
    cases p
    · exact h
    · exact h
  · intro i; have hi := Fin.eq_zero i; subst i
    have h := rook_check p
    cases p
    · exact h
    · exact h
  · intro i src dst pr piece hm hp; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (knightSq p) (dstSq p) false = .boardMove src dst pr at hm
    cases hm
    change (s0 p).board.grid (knightSq p) = some piece at hp
    have hp' : (s0 p).board.grid (knightSq p) = some ⟨p, .knight⟩ := by cases p <;> rfl
    rw [hp'] at hp
    cases hp
    exact Or.inl (by cases p <;> decide)

-- The knight, two squares from the enemy king, does not glare.
private theorem knight_not_glares (p : Player) :
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (0 : Fin 2) (knightSq p) := by
  rintro ⟨piece, hp, ha⟩
  change (s0 p).board.grid (knightSq p) = some piece at hp
  have hp' : (s0 p).board.grid (knightSq p) = some ⟨p, .knight⟩ := by cases p <;> rfl
  rw [hp'] at hp
  cases hp
  rcases ha with hs | ⟨_, hsd, _⟩
  · revert hs
    cases p <;> decide
  · simp [PieceType.slideDirs] at hsd

private theorem not_periodic (p : Player) : ¬ (tr p).IsPeriodic := by
  intro h
  have ht := congrArg BoardState.turn h
  change p.opponent = p at ht
  cases p <;> cases ht

-- Both first movers. Every premise but periodicity holds, the trace is not
-- periodic, the moved knight does not glare, and its owner's forward rank rises.
example (p : Player) :
    premises p ∧ ¬ (tr p).IsPeriodic ∧
    (tr p).moves (0 : Fin 1) = .boardMove (knightSq p) (dstSq p) false ∧
    ((tr p).before (0 : Fin 1)).board.grid (knightSq p) = some ⟨p, .knight⟩ ∧
    ¬ (tr p).GlaresAtEnemyKing (kpc p) (0 : Fin 2) (knightSq p) ∧
    forwardRank p (knightSq p) < forwardRank p (dstSq p) := by
  refine ⟨premises_hold p, not_periodic p, rfl, by cases p <;> rfl, knight_not_glares p,
    by cases p <;> decide⟩

end ForwardPotentialTests
end MPC
