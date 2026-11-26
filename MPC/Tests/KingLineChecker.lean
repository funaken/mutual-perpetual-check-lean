import MPC.Basic.Lemmas
import MPC.Legacy.CheckCompatibility
import MPC.Geometry.KingLineChecker
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.KingLineChecker

Proposition 3.6 needs drops to land on empty squares. For both first movers, a
periodic two-move trace has the kings on a file and the two sides alternately
re-drop a rook on the square between them. Each drop overwrites the other
side's rook and checks the enemy king. The trace satisfies every other premise
(placement, initial opponent safety, self-safety, mutual check, the movement
condition, periodicity), yet a checker stands on the kings' line. So
`DropDestinationsEmpty` cannot be dropped. Empty hands make each re-drop free,
which the model does not forbid.

A one-move capture also checks that capturing lowers the number of occupied
squares, and a concrete triple checks `collinear_of_line_params`. The board
updates make no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "King line checker verification must not import GameSeq"

namespace MPC
namespace KingLineCheckerTests

-- Three points on the diagonal through (0,0) are collinear.
example : Geometry.collinear (Pos.toInt (1, 1)) (Pos.toInt (3, 3)) (Pos.toInt (6, 6)) :=
  collinear_of_line_params (0, 0) (1, 1) (3, 3) (6, 6) (1, 1) 1 3 6 (by decide) (by decide)
    (by decide)

/-! ## Re-dropping on the kings' line -/

private def own : Pos := (0, 0)
private def mid : Pos := (0, 4)
private def opp : Pos := (0, 8)

-- The kings at the ends of the file and a rook between them, owned by `r`.
private def board (p r : Player) (t : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = own then some ⟨p, .king⟩
        else if q = opp then some ⟨p.opponent, .king⟩
        else if q = mid then some ⟨r, .rook⟩ else none
      hand := fun _ => ∅ }
    turn := t }
private def redrop : Move := .dropMove .rook mid
private def kpD (p : Player) : Fin 3 → Player → Pos := fun _ o => if o = p then own else opp

private theorem redrop_eq (p r t : Player) :
    applyMove (board p r t) redrop = board p t t.opponent := by
  simp only [applyMove, redrop, board, Board.setGrid, Board.removeFromHand, BoardState.mk.injEq,
    Board.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · funext q
    by_cases h1 : q = mid
    · subst h1
      simp [own, opp, mid]
    · simp only [ite_eq_right h1]
  · funext q
    split_ifs <;> simp

private def tr (p : Player) : MoveTrace where
  len := 2
  states := fun k => match k.val with
    | 1 => board p p p.opponent
    | _ => board p p.opponent p
  moves := fun _ => redrop

-- A rook of either owner on `mid` attacks both kings along the clear file.
private theorem rook_up (b : Board) (o : Player) (h5 : b.grid (0, 5) = none)
    (h6 : b.grid (0, 6) = none) (h7 : b.grid (0, 7) = none) :
    attacksOriented b o .rook mid opp := by
  have hc := pathClear_iff_of_exact_steps b mid opp (0, 1) 4 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine Or.inr ⟨(0, 1), by cases o <;> decide, by decide, 4, by decide, by decide, by decide,
    hc.mpr ?_⟩
  intro j hj hjn hob
  interval_cases j
  · exact h5
  · exact h6
  · exact h7

private theorem rook_down (b : Board) (o : Player) (h3 : b.grid (0, 3) = none)
    (h2 : b.grid (0, 2) = none) (h1 : b.grid (0, 1) = none) :
    attacksOriented b o .rook mid own := by
  have hc := pathClear_iff_of_exact_steps b mid own (0, -1) 4 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine Or.inr ⟨(0, -1), by cases o <;> decide, by decide, 4, by decide, by decide, by decide,
    hc.mpr ?_⟩
  intro j hj hjn hob
  interval_cases j
  · exact h3
  · exact h2
  · exact h1

private theorem placed (p r t : Player) :
    KingsWellPlaced (board p r t).board (fun o => if o = p then own else opp) := by
  intro o q
  cases p <;> cases o <;> by_cases h1 : q = own <;> by_cases h2 : q = opp <;>
    by_cases h3 : q = mid <;> simp_all [board, own, opp, mid, Player.opponent]

-- Only the enemy king could attack, and it is far away; the rook belongs to the
-- side being checked or to nobody threatening this king.
private theorem safe (p r t o : Player) (hr : r = o) :
    ¬ inCheckOriented (board p r t).board o (if o = p then own else opp) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [board] at hp
  split_ifs at hp <;> cases hp
  all_goals first
    | (rw [hr] at ho; cases o <;> cases ho)
    | (cases p <;> cases o <;> cases ho; done)
    | (rename_i h; subst h
       rcases ha with hs | ⟨_, hsd, _⟩
       · revert hs
         cases p <;> cases o <;> decide
       · simp [PieceType.slideDirs] at hsd)

private theorem check (p r : Player) (t : Player) :
    inCheckOriented (board p r t).board r.opponent (if r.opponent = p then own else opp) := by
  refine ⟨mid, ⟨r, .rook⟩, by simp [board, own, opp, mid], by rw [Player.opponent_opponent], ?_⟩
  cases p <;> cases r
  · exact rook_up _ _ (by simp [board, own, opp, mid]) (by simp [board, own, opp, mid])
      (by simp [board, own, opp, mid])
  · exact rook_down _ _ (by simp [board, own, opp, mid]) (by simp [board, own, opp, mid])
      (by simp [board, own, opp, mid])
  · exact rook_down _ _ (by simp [board, own, opp, mid]) (by simp [board, own, opp, mid])
      (by simp [board, own, opp, mid])
  · exact rook_up _ _ (by simp [board, own, opp, mid]) (by simp [board, own, opp, mid])
      (by simp [board, own, opp, mid])

-- Both first movers. Every premise of Proposition 3.6 except
-- `DropDestinationsEmpty` holds, and after the first move a checker stands on the
-- kings' line.
example (p : Player) :
    (tr p).FollowsTransitions ∧ (tr p).BoardMoveSourcesOwned ∧
    (tr p).KingsWellPlaced (kpD p) ∧ (tr p).EveryMoveLeavesOwnKingSafe (kpD p) ∧
    (tr p).InitialOpponentKingSafe (kpD p) ∧ (tr p).EveryMoveChecksOpponent (kpD p) ∧
    (tr p).BoardMovesFollowCanMoveToOriented ∧ (tr p).IsPeriodic ∧ 0 < (tr p).len ∧
    ¬ (tr p).DropDestinationsEmpty ∧ (tr p).CheckerOnKingLine (kpD p) (1 : Fin 3) mid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, show 0 < 2 by decide, ?_, ?_⟩
  · intro i
    match i with
    | ⟨0, _⟩ =>
      show board p p p.opponent = applyMove (board p p.opponent p) redrop
      rw [redrop_eq]
    | ⟨1, _⟩ =>
      show board p p.opponent p = applyMove (board p p p.opponent) redrop
      rw [redrop_eq, Player.opponent_opponent]
  · intro i src dst pr hm
    cases hm
  · intro k
    match k with
    | ⟨0, _⟩ => exact placed p p.opponent p
    | ⟨1, _⟩ => exact placed p p p.opponent
    | ⟨2, _⟩ => exact placed p p.opponent p
  · intro i
    match i with
    | ⟨0, _⟩ => exact safe p p p.opponent p rfl
    | ⟨1, _⟩ =>
      have h := safe p p.opponent p p.opponent rfl
      exact h
  · exact safe p p.opponent p p.opponent rfl
  · intro i
    match i with
    | ⟨0, _⟩ =>
      have h := check p p p.opponent
      exact h
    | ⟨1, _⟩ =>
      have h := check p p.opponent p
      exact h
  · intro i src dst pr piece hm
    cases hm
  · intro h
    have h' := h (0 : Fin 2) .rook mid rfl
    change (board p p.opponent p).board.grid mid = none at h'
    simp [board, own, opp, mid] at h'
  · refine ⟨⟨p, .rook⟩, by simp [tr, board, own, opp, mid], ?_, ?_⟩
    · cases p <;> exact rook_up _ _ (by simp [tr, board, own, opp, mid])
        (by simp [tr, board, own, opp, mid]) (by simp [tr, board, own, opp, mid])
    · cases p <;> unfold Geometry.collinear <;> decide

/-! ## Capturing lowers the number of occupied squares -/

private def c0 (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = (0, 0) then some ⟨p, .rook⟩
        else if q = (0, 1) then some ⟨p.opponent, .pawn⟩ else none
      hand := fun _ => ∅ }
    turn := p }

example (p : Player) :
    ((MoveTrace.single (c0 p) (.boardMove (0, 0) (0, 1) false)).occupiedSquares 1).card <
      ((MoveTrace.single (c0 p) (.boardMove (0, 0) (0, 1) false)).occupiedSquares 0).card := by
  refine MoveTrace.occupiedSquares_card_succ_lt_of_capture _
    (MoveTrace.single_followsTransitions _ _) ?_ (0 : Fin 1) (0, 0) (0, 1) false rfl
    (by decide) (by simp [MoveTrace.before, MoveTrace.single, c0])
  intro i src dst pr hm
  have hi := Fin.eq_zero i
  subst i
  cases hm
  exact ⟨⟨p, .rook⟩, by simp [MoveTrace.before, MoveTrace.single, c0], rfl⟩

end KingLineCheckerTests
end MPC
