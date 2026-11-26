import MPC.Chess.SecondCrossingMoves
import Mathlib.Tactic.FinCases

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

-- Ordinary and wrapped intervals, including both copies of the period boundary.
example : cyclicBetween (1 : Fin 5) 3 2 ∧ ¬ cyclicBetween (1 : Fin 5) 3 4 ∧
    cyclicBetween (3 : Fin 5) 1 4 ∧ cyclicBetween (3 : Fin 5) 1 0 ∧
    ¬ cyclicBetween (3 : Fin 5) 1 2 := by decide

-- All states can belong to the stay while the departing move is excluded.
example : (∀ k : Fin 5, cyclicBetween (3 : Fin 5) 2 k) ∧
    ¬ cyclicStepBetween (3 : Fin 5) 2 (2 : Fin 4) ∧
    cyclicStepBetween (3 : Fin 5) 2 (3 : Fin 4) ∧
    cyclicStepBetween (3 : Fin 5) 2 (0 : Fin 4) := by decide

example : cyclicBetween (4 : Fin 5) 0 4 ∧ cyclicBetween (4 : Fin 5) 0 0 ∧
    (∀ m : Fin 4, ¬ cyclicStepBetween (4 : Fin 5) 0 m) ∧
    (∀ k : Fin 5, cyclicBetween (2 : Fin 5) 2 k ↔ k = 2) ∧
    (∀ m : Fin 4, ¬ cyclicStepBetween (2 : Fin 5) 2 m) := by decide

example : cyclicBetween (0 : Fin 1) 0 0 ∧
    ∀ m : Fin 0, ¬ cyclicStepBetween (0 : Fin 1) 0 m := by decide

example {n : ℕ} {a b : Fin (n + 1)} {m : Fin n} (h : cyclicStepBetween a b m) :
    cyclicBetween a b m.castSucc ∧ cyclicBetween a b m.succ := cyclicStepBetween_states h

private def stayBoard (c : Color) : Board := fun q =>
  if q = (7, 7) then some ⟨c, .king⟩
  else if q = (0, 6) then some ⟨c.opponent, .king⟩
  else if q = (0, 0) then some ⟨c, .rook⟩
  else if q = (2, 1) ∨ q = (0, 4) then some ⟨c, .knight⟩
  else if q = (7, 0) then some ⟨c.opponent, .knight⟩ else none

private def stayKings (c : Color) : Color → Pos := fun o => if o = c then (7, 7) else (0, 6)

private def stayMove : ℕ → Move
  | 0 => .boardMove (2, 1) (0, 2) none
  | 1 => .boardMove (7, 0) (5, 1) none
  | _ => .boardMove (0, 4) (2, 5) none

private def stayState (c : Color) : ℕ → Position
  | 0 => ⟨stayBoard c, c, {}, none⟩
  | n + 1 => applyMove (stayState c n) (stayMove n)

private def stayTrace (c : Color) : MoveTrace where
  len := 3
  states := fun k => stayState c k.val
  moves := fun m => stayMove m.val

private theorem stay_legal (c : Color) : (stayTrace c).FollowsLegalMoves := by
  intro m
  refine ⟨stayKings c, ?_, rfl⟩
  have h : ∀ m : Fin 3, LegalMove (stayState c m.val) (stayMove m.val) (stayKings c) := by
    cases c <;> decide
  exact h m

private theorem stay_ordinary (c : Color) : (stayTrace c).OrdinaryMoves := by
  intro m
  fin_cases m
  · exact ⟨(2, 1), (0, 2), rfl⟩
  · exact ⟨(7, 0), (5, 1), rfl⟩
  · exact ⟨(0, 4), (2, 5), rfl⟩

private theorem stay_destinations (c : Color) :
    (stayTrace c).GlaringDestinationsCheck (fun _ => stayKings c) := by
  intro m src dst hm hg
  fin_cases m
  · change Move.boardMove (2, 1) (0, 2) none = .boardMove src dst none at hm
    cases hm
    have hn : ¬ (stayTrace c).GlaresAtEnemyKing (fun _ => stayKings c) 1 (0, 2) := by cases c <;> decide
    exact (hn hg).elim
  · change Move.boardMove (7, 0) (5, 1) none = .boardMove src dst none at hm
    cases hm
    have hn : ¬ (stayTrace c).GlaresAtEnemyKing (fun _ => stayKings c) 2 (5, 1) := by cases c <;> decide
    exact (hn hg).elim
  · change Move.boardMove (0, 4) (2, 5) none = .boardMove src dst none at hm
    cases hm
    cases c <;> decide


example (c : Color) : (stayTrace c).KingsWellPlaced (fun _ => stayKings c) := by
  change ∀ k : Fin 4, KingsWellPlaced (stayState c k.val).board (stayKings c)
  cases c <;> decide

-- A genuine local application: a knight arrives on the rook's line, stays for
-- two further moves, and the rook is retained. No periodic mutual-check example
-- is asserted. Both colors satisfy the explicit local interface.
example (c : Color) :
    (∀ k : Fin 4, ((stayTrace c).states k).board (0, 0) = some ⟨c, .rook⟩ ∧
      (stayTrace c).GlaresAtEnemyKing (fun _ => stayKings c) k (0, 0)) ∧
    (∀ m : Fin 3, ¬ ((stayTrace c).moves m).Touches ((stayTrace c).before m).turn (0, 0)) := by
  have hQ : ((stayTrace c).states (3 : Fin 4)).board (0, 0) = some ⟨c, .rook⟩ := by cases c <;> decide
  have hg : (stayTrace c).GlaresAtEnemyKing (fun _ => stayKings c) 3 (0, 0) := by cases c <;> decide
  have hA : Between (0, 0) (stayKings c c.opponent) (0, 2) := by cases c <;> decide
  have hocc : ∀ k : Fin 4, (0 : Fin 4) < k → k ≤ 3 → ((stayTrace c).states k).board (0, 2) ≠ none := by
    cases c <;> decide
  have h := (stayTrace c).line_witness_persists (fun _ => stayKings c) (stay_legal c)
    (stay_ordinary c) (fun _ => rfl) (stay_destinations c) (a := 0) (b := 3)
    (0, 0) (0, 2) ⟨c, .rook⟩ hQ hg (Or.inr (Or.inl rfl)) hA hocc
  exact ⟨fun k => h.1 k (Fin.zero_le _) (Fin.le_last _),
    fun m => h.2 m (Fin.zero_le _) (Fin.le_last _)⟩

-- The witness glares through an occupied movable blocker but does not actually
-- attack through it. Its interval is not a claim of continuous real check.
example (c : Color) :
    ∀ k : Fin 4, (1 : Fin 4) ≤ k → ¬ attacks ((stayTrace c).states k).board ⟨c, .rook⟩ (0, 0) (0, 6) := by
  cases c <;> decide

-- A legal periodic knight cycle exercises first departure independently of
-- mutual checking, which the final cyclic witness theorem additionally needs.
private def cycleBoard : Board := fun q =>
  if q = kingHome .white then some ⟨.white, .king⟩
  else if q = kingHome .black then some ⟨.black, .king⟩
  else if q = (1, 0) then some ⟨.white, .knight⟩
  else if q = (1, 7) then some ⟨.black, .knight⟩ else none

private def cycleMove (c : Color) : ℕ → Move
  | 0 => .boardMove (1, c.homeRank) (2, c.doubleStepTargetRank) none
  | 1 => .boardMove (1, c.opponent.homeRank) (2, c.opponent.doubleStepTargetRank) none
  | 2 => .boardMove (2, c.doubleStepTargetRank) (1, c.homeRank) none
  | _ => .boardMove (2, c.opponent.doubleStepTargetRank) (1, c.opponent.homeRank) none

private def cycleState (c : Color) : ℕ → Position
  | 0 => ⟨cycleBoard, c, {}, none⟩
  | n + 1 => applyMove (cycleState c n) (cycleMove c n)

private def cycleTrace (c : Color) : MoveTrace where
  len := 4
  states := fun k => cycleState c k.val
  moves := fun m => cycleMove c m.val

private theorem cycle_legal (c : Color) : (cycleTrace c).FollowsLegalMoves := by
  intro m
  refine ⟨kingHome, ?_, rfl⟩
  have h : ∀ m : Fin 4, LegalMove (cycleState c m.val) (cycleMove c m.val) kingHome := by cases c <;> decide
  exact h m

private theorem cycle_periodic (c : Color) : (cycleTrace c).BoardTurnPeriodic := by
  constructor
  · funext q
    have h : ∀ q, (cycleState c 4).board q = cycleBoard q := by cases c <;> decide
    exact h q
  · cases c <;> rfl

private theorem cycle_ordinary (c : Color) : (cycleTrace c).OrdinaryMoves := by
  intro m
  fin_cases m
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

example (c : Color) :
    ∃ (j : Fin 4) (dst : Pos), (1 : Fin 5) ≤ j.castSucc ∧
      (cycleTrace c).moves j = .boardMove (2, c.doubleStepTargetRank) dst none ∧
      ∀ k : Fin 5, (1 : Fin 5) ≤ k → k ≤ j.castSucc →
        ((cycleTrace c).states k).board (2, c.doubleStepTargetRank) =
          ((cycleTrace c).states 1).board (2, c.doubleStepTargetRank) := by
  apply (cycleTrace c).departure_of_occupied_of_periodic (cycle_legal c) (cycle_periodic c)
    (cycle_ordinary c) (2, c.doubleStepTargetRank) 1
  · cases c <;> decide
  · refine ⟨(2 : Fin 4), (show (1 : Fin 5) ≤ (2 : Fin 4).castSucc by decide), ?_⟩
    cases c <;> decide

-- The first and last moves can be departures; beyond the final state no move
-- index is available. These facts do not supply mutual-check periodicity.
example (c : Color) :
    ((cycleTrace c).moves (0 : Fin 4)).Touches ((cycleTrace c).before (0 : Fin 4)).turn (1, c.homeRank) ∧
    ((cycleTrace c).moves (3 : Fin 4)).Touches ((cycleTrace c).before (3 : Fin 4)).turn (2, c.opponent.doubleStepTargetRank) ∧
    ¬ ∃ m : Fin 4, (4 : Fin 5) ≤ m.castSucc := by
  cases c <;> decide

example (c : Color) : ¬ (cycleTrace c).EveryMoveChecksOpponent (fun _ => kingHome) := by
  intro h
  have h0 := h (0 : Fin 4)
  have hn : ¬ inCheck (cycleState c 1).board c.opponent (kingHome c.opponent) := by cases c <;> decide
  exact hn h0

example (c : Color) :
    ((cycleTrace c).states (2 : Fin 5)).board (2, c.doubleStepTargetRank) =
      ((cycleTrace c).states (1 : Fin 5)).board (2, c.doubleStepTargetRank) := by
  apply (cycleTrace c).board_eq_of_untouched (cycle_legal c) _ (show (1 : Fin 5) ≤ 2 by decide)
  have h : ∀ m : Fin (cycleTrace c).len,
      (1 : Fin ((cycleTrace c).len + 1)) ≤ m.castSucc → m.castSucc < 2 →
      ¬ ((cycleTrace c).moves m).Touches ((cycleTrace c).before m).turn (2, c.doubleStepTargetRank) := by
    cases c <;> decide
  exact h

example (c : Color) :
    ¬ ((cycleTrace c).moves (1 : Fin 4)).Touches ((cycleTrace c).before (1 : Fin 4)).turn (2, c.doubleStepTargetRank) := by
  apply (cycleTrace c).not_touches_of_occupied_before_after (cycle_legal c) (cycle_periodic c)
    (cycle_ordinary c) (1 : Fin 4) (2, c.doubleStepTargetRank)
  · cases c <;> decide
  · cases c <;> decide

-- Every occupied knight in every state has an untouched cyclic stay ending
-- in its departure. This includes immediate departures and wraparound at 3/4.
example (c owner : Color) (k : Fin 5) (C : Pos)
    (hX : ((cycleTrace c).states k).board C = some ⟨owner, .knight⟩) :
    ∃ (j : Fin 4) (dst : Pos), (cycleTrace c).moves j = .boardMove C dst none ∧
      ((cycleTrace c).before j).board C = some ⟨owner, .knight⟩ ∧
      (∀ l, cyclicBetween k j.castSucc l →
        ((cycleTrace c).states l).board C = some ⟨owner, .knight⟩) ∧
      ∀ m, cyclicStepBetween k j.castSucc m →
        ¬ ((cycleTrace c).moves m).Touches ((cycleTrace c).before m).turn C := by
  have hn : ∀ (k : Fin 5) (C : Pos),
      ((cycleTrace c).states k).board C = some ⟨owner, .knight⟩ → ¬ (cycleTrace c).ImmovableAt C := by
    cases c <;> cases owner <;> decide
  exact (cycleTrace c).occupied_piece_departs_of_not_immovable (cycle_legal c) (cycle_periodic c)
    (cycle_ordinary c) k C _ hX (hn k C hX)

-- At the final state there is no later linear move; departure wraps to 0.
example (c : Color) : ∃ (j : Fin 4) (dst : Pos), j = 0 ∧
    (cycleTrace c).moves j = .boardMove (1, c.homeRank) dst none ∧
    ∀ m, cyclicStepBetween (4 : Fin 5) j.castSucc m →
      ¬ ((cycleTrace c).moves m).Touches ((cycleTrace c).before m).turn (1, c.homeRank) := by
  obtain ⟨j, dst, hm, _, _, hun⟩ := (cycleTrace c).occupied_piece_departs_of_not_immovable
    (cycle_legal c) (cycle_periodic c) (cycle_ordinary c) 4 (1, c.homeRank) ⟨c, .knight⟩
    (by cases c <;> decide) (by cases c <;> decide)
  refine ⟨j, dst, ?_, hm, hun⟩
  fin_cases j <;> cases c <;> simp_all [cycleTrace, cycleMove, Color.homeRank, Color.doubleStepTargetRank, Color.opponent]

private def rayStart (axis : Fin 4) : Pos :=
  match axis.val with | 0 => (0, 3) | 1 => (3, 0) | 2 => (0, 0) | _ => (0, 6)
private def rayEnd (axis : Fin 4) : Pos :=
  match axis.val with | 0 => (6, 3) | 1 => (3, 6) | 2 => (6, 6) | _ => (6, 0)

-- Adding a blocker on each of the eight queen rays removes the attack. The
-- contrapositive of the pure update lemma identifies the destination on the line.
example (c : Color) (axis : Fin 4) (reverse : Bool) :
    let a := if reverse then rayEnd axis else rayStart axis
    let t := if reverse then rayStart axis else rayEnd axis
    Between a t (3, 3) := by
  let b : Board := fun q => if q = (7, 7) then some ⟨c, .knight⟩ else none
  have h : ∀ axis : Fin 4, ∀ reverse : Bool,
      let a := if reverse then rayEnd axis else rayStart axis
      let t := if reverse then rayStart axis else rayEnd axis
      attacks b ⟨c, .queen⟩ a t ∧
        ¬ attacks (b.relocate (7, 7) (3, 3) none) ⟨c, .queen⟩ a t := by
    cases c <;> decide
  by_contra hn
  exact (h axis reverse).2 (attacks_relocate_of_not_between b ⟨c, .queen⟩ _ _ (7, 7) (3, 3) none
    (h axis reverse).1 hn)

end MPC.Chess.Tests
