import MPC.Chess.Attack

/-! Finite trace data and separate predicates. No movement, immobility, or
king-location assumptions are hidden in the data structure. -/

namespace MPC.Chess

structure MoveTrace where
  len : ℕ
  states : Fin (len + 1) → Position
  moves : Fin len → Move

namespace MoveTrace

def before (tr : MoveTrace) (i : Fin tr.len) : Position := tr.states i.castSucc

def after (tr : MoveTrace) (i : Fin tr.len) : Position := tr.states i.succ

def Follows (tr : MoveTrace) (step : Position → Move → Position → Prop) : Prop :=
  ∀ i, step (tr.before i) (tr.moves i) (tr.after i)

def KingsWellPlaced (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos) : Prop :=
  ∀ i, MPC.Chess.KingsWellPlaced (tr.states i).board (kp i)

def EveryMoveChecksOpponent (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) : Prop :=
  ∀ i, inCheck (tr.after i).board (tr.before i).turn.opponent
    (kp i.succ (tr.before i).turn.opponent)

/-- Only board and side to move recur. Castling/en-passant data may differ;
this deliberately states a weaker recurrence than equality of full positions. -/
def BoardTurnPeriodic (tr : MoveTrace) : Prop :=
  (tr.states (Fin.last tr.len)).board = (tr.states 0).board ∧
    (tr.states (Fin.last tr.len)).turn = (tr.states 0).turn

def empty (initial : Position) : MoveTrace where
  len := 0
  states := fun _ => initial
  moves := Fin.elim0

def single (initial final : Position) (move : Move) : MoveTrace where
  len := 1
  states := fun i => if i.val = 0 then initial else final
  moves := fun _ => move

@[simp] theorem single_before (initial final : Position) (move : Move) :
    (single initial final move).before (0 : Fin 1) = initial := rfl

@[simp] theorem single_after (initial final : Position) (move : Move) :
    (single initial final move).after (0 : Fin 1) = final := rfl

theorem single_follows_iff (initial final : Position) (move : Move)
    (step : Position → Move → Position → Prop) :
    (single initial final move).Follows step ↔ step initial move final := by
  constructor
  · exact fun h => h (0 : Fin 1)
  · intro h i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    exact h

end MoveTrace
end MPC.Chess
