import MPC.Trace.KingPlacementTrace
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Lean
/-!
# MPC.Tests.KingPlacementTrace

Trace-wide placement is derived from initial placement and local board conditions.
The examples move both kings and then preserve their new positions through a
non-king move (with either promotion flag) and a drop. No full legality is claimed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "King placement trace verification must not import GameSeq"

namespace MPC

private def initialPositions : Player → Pos
  | .sente => (0, 0)
  | .gote => (8, 8)

private def movedPositions : Player → Pos
  | .sente => (1, 0)
  | .gote => (7, 8)

private def initialState (turn : Player) : BoardState :=
  { board :=
      { grid := fun q => if q = (0, 0) then some ⟨.sente, .king⟩
          else if q = (8, 8) then some ⟨.gote, .king⟩
          else if q = (4, 4) then some ⟨turn, .rook⟩ else none
        hand := fun _ => ∅ }
    turn := turn }

private theorem initial_placed (turn : Player) :
    KingsWellPlaced (initialState turn).board initialPositions := by
  intro owner q
  cases owner <;> by_cases h0 : q = (0, 0) <;> by_cases h8 : q = (8, 8) <;>
    by_cases h4 : q = (4, 4) <;> simp_all [initialState, initialPositions]

private def fourMoves (turn : Player) (promote : Bool) (i : Fin 4) : Move :=
  match i.val with
  | 0 => .boardMove (initialPositions turn) (movedPositions turn) false
  | 1 => .boardMove (initialPositions turn.opponent) (movedPositions turn.opponent) false
  | 2 => .boardMove (4, 4) (5, 4) promote
  | _ => .dropMove .pawn (4, 5)

private def fourSteps (turn : Player) (promote : Bool) : MoveTrace :=
  { len := 4
    states := Fin.induction (initialState turn)
      (fun i bs => applyMove bs (fourMoves turn promote i))
    moves := fourMoves turn promote }

private theorem fourSteps_transitions (turn : Player) (promote : Bool) :
    (fourSteps turn promote).FollowsTransitions := by
  intro i
  simp [MoveTrace.before, MoveTrace.after, fourSteps]
  exact Fin.induction_succ (motive := fun _ => BoardState) _ _ i

private theorem fourSteps_avoidsKings (turn : Player) (promote : Bool) :
    (fourSteps turn promote).MoveDestinationsAvoidKings := by
  intro i
  change Fin 4 at i
  fin_cases i <;> intro owner <;> cases owner <;> cases turn <;> cases promote <;> decide

private theorem fourSteps_nonKingDrops (turn : Player) (promote : Bool) :
    (fourSteps turn promote).DropMovesAreNonKings := by
  intro i pt dst hm
  change Fin 4 at i
  fin_cases i <;> simp [fourSteps, fourMoves] at hm
  obtain ⟨rfl, rfl⟩ := hm
  decide

-- All-state consistency is a conclusion, including both starting turns and
-- both promotion flags, rather than an input checked independently per state.
private theorem fourSteps_placed (turn : Player) (promote : Bool) :
    (fourSteps turn promote).KingsWellPlaced
      ((fourSteps turn promote).kingPositionsFrom initialPositions) :=
  (fourSteps turn promote).kingsWellPlaced_kingPositionsFrom initialPositions
    (fourSteps_transitions turn promote) (fourSteps_avoidsKings turn promote)
    (fourSteps_nonKingDrops turn promote) (initial_placed turn)

example (turn : Player) (promote : Bool) :
    let tr := fourSteps turn promote
    tr.kingPositionsFrom initialPositions 0 = initialPositions ∧
    tr.kingPositionsFrom initialPositions 1 turn = movedPositions turn ∧
    tr.kingPositionsFrom initialPositions 1 turn.opponent = initialPositions turn.opponent ∧
    tr.kingPositionsFrom initialPositions 2 = movedPositions ∧
    tr.kingPositionsFrom initialPositions 3 = movedPositions ∧
    tr.kingPositionsFrom initialPositions 4 = movedPositions := by
  cases turn <;> cases promote <;> refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;>
    funext owner <;> cases owner <;> rfl

-- Actual king positions change, while the later rook promotion and pawn drop
-- affect only non-king squares. This also checks the final state and turn order.
example (turn : Player) (promote : Bool) :
    let tr := fourSteps turn promote
    tr.KingsWellPlaced (tr.kingPositionsFrom initialPositions) ∧
    (tr.states 1).board.grid (initialPositions turn) = none ∧
    (tr.states 2).board.grid (initialPositions turn.opponent) = none ∧
    (tr.states 3).board.grid (5, 4) =
      some ⟨turn, if promote then .dragon else .rook⟩ ∧
    (tr.states 4).board.grid (4, 5) = some ⟨turn.opponent, .pawn⟩ ∧
    (tr.states 4).turn = turn := by
  refine ⟨fourSteps_placed turn promote, ?_⟩
  cases turn <;> cases promote <;> decide

example (turn : Player) (promote : Bool)
    (other : Fin 5 → Player → Pos)
    (h : (fourSteps turn promote).KingsWellPlaced other) :
    (fourSteps turn promote).kingPositionsFrom initialPositions = other :=
  (fourSteps turn promote).kingPositionsFrom_eq_of_kingsWellPlaced initialPositions
    (fourSteps_transitions turn promote) (fourSteps_avoidsKings turn promote)
    (fourSteps_nonKingDrops turn promote) (initial_placed turn) other h

private def noSteps (bs : BoardState) : MoveTrace :=
  { len := 0, states := fun _ => bs, moves := Fin.elim0 }

-- With no moves, transition/drop/destination conditions are vacuous, but
-- placement is equivalent to the initial board condition, not vacuous.
example (bs : BoardState) (initial : Player → Pos) :
    (noSteps bs).FollowsTransitions ∧
    (noSteps bs).MoveDestinationsAvoidKings ∧ (noSteps bs).DropMovesAreNonKings ∧
    ((noSteps bs).KingsWellPlaced ((noSteps bs).kingPositionsFrom initial) ↔
      KingsWellPlaced bs.board initial) := by
  refine ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
    (fun i => Fin.elim0 i), ?_⟩
  constructor
  · intro h; exact h 0
  · intro h i
    change Fin 1 at i
    have hi := Fin.eq_zero i
    subst i
    exact h

example (turn : Player) (promote : Bool) :
    ¬ (MoveTrace.single (initialState turn)
      (.boardMove (4, 4) (initialPositions turn.opponent) promote)).MoveDestinationsAvoidKings := by
  intro h
  exact h (0 : Fin 1) turn.opponent ((initial_placed turn).king_present turn.opponent)

example (turn : Player) :
    ¬ (MoveTrace.single (initialState turn)
      (.dropMove .pawn (initialPositions turn))).MoveDestinationsAvoidKings := by
  intro h
  exact h (0 : Fin 1) turn ((initial_placed turn).king_present turn)

-- King drops are rejected even at an empty square; neither external condition
-- takes a generated king-position sequence as an argument.
example (turn : Player) :
    (MoveTrace.single (initialState turn) (.dropMove .king (4, 5))).MoveDestinationsAvoidKings ∧
    ¬ (MoveTrace.single (initialState turn) (.dropMove .king (4, 5))).DropMovesAreNonKings := by
  constructor
  · intro i owner
    change Fin 1 at i
    have hi := Fin.eq_zero i
    subst i
    cases turn <;> cases owner <;> decide
  · intro h
    exact h (0 : Fin 1) .king (4, 5) rfl rfl

end MPC
