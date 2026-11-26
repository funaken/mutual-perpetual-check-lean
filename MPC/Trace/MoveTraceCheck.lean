import MPC.Trace.KingPlacementTrace
/-!
# MPC.Trace.MoveTraceCheck

External checking and self-safety conditions for independent traces. The mover
is the before-state turn, while the board and king positions are from the after
state. Neither condition follows just from transitions or consistent placement.
-/

namespace MPC.MoveTrace

/-- Every move checks the opposing king at its after-state position.
    Actual king presence/uniqueness is a separate placement condition. -/
def EveryMoveChecksOpponent (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos) : Prop :=
  ∀ i : Fin tr.len, inCheckOriented (tr.after i).board (tr.before i).turn.opponent
    (kingPos i.succ (tr.before i).turn.opponent)

/-- Every move leaves the mover's king safe at its after-state position.
    No safety assertion is made about the initial state. -/
def EveryMoveLeavesOwnKingSafe (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos) : Prop :=
  ∀ i : Fin tr.len, ¬ inCheckOriented (tr.after i).board (tr.before i).turn
    (kingPos i.succ (tr.before i).turn)

theorem everyMoveChecksOpponent_iff_after_turn (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions) :
    tr.EveryMoveChecksOpponent kingPos ↔
      ∀ i : Fin tr.len, inCheckOriented (tr.after i).board (tr.after i).turn
        (kingPos i.succ (tr.after i).turn) := by
  simp only [EveryMoveChecksOpponent, tr.turn_after_move ht]

theorem everyMoveLeavesOwnKingSafe_iff_after_opponent (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions) :
    tr.EveryMoveLeavesOwnKingSafe kingPos ↔
      ∀ i : Fin tr.len, ¬ inCheckOriented (tr.after i).board (tr.after i).turn.opponent
        (kingPos i.succ (tr.after i).turn.opponent) := by
  have hop (p : Player) : p.opponent.opponent = p := by cases p <;> rfl
  simp only [EveryMoveLeavesOwnKingSafe, tr.turn_after_move ht, hop]

/-- Consistent placement identifies the supplied target with an actual king. -/
theorem everyMoveChecksOpponent_iff_exists_king (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos) (hk : tr.KingsWellPlaced kingPos) :
    tr.EveryMoveChecksOpponent kingPos ↔
      ∀ i : Fin tr.len, ∃ pos : Pos,
        (tr.after i).board.grid pos = some ⟨(tr.before i).turn.opponent, .king⟩ ∧
        inCheckOriented (tr.after i).board (tr.before i).turn.opponent pos := by
  exact forall_congr' fun i => (hk i.succ).inCheckOriented_iff_exists_king _

theorem everyMoveLeavesOwnKingSafe_iff_no_checked_king (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos) (hk : tr.KingsWellPlaced kingPos) :
    tr.EveryMoveLeavesOwnKingSafe kingPos ↔
      ∀ i : Fin tr.len, ¬ ∃ pos : Pos,
        (tr.after i).board.grid pos = some ⟨(tr.before i).turn, .king⟩ ∧
        inCheckOriented (tr.after i).board (tr.before i).turn pos := by
  exact forall_congr' fun i => not_congr ((hk i.succ).inCheckOriented_iff_exists_king _)

/-- Initial placement and the destination and non-king-drop conditions supply all-state placement;
    checking itself remains an independent proposition on either side. -/
theorem everyMoveChecksOpponent_kingPositionsFrom_iff_exists_king (tr : MoveTrace)
    (initial : Player → Pos) (ht : tr.FollowsTransitions)
    (ha : tr.MoveDestinationsAvoidKings) (hd : tr.DropMovesAreNonKings)
    (h0 : MPC.KingsWellPlaced (tr.states 0).board initial) :
    tr.EveryMoveChecksOpponent (tr.kingPositionsFrom initial) ↔
      ∀ i : Fin tr.len, ∃ pos : Pos,
        (tr.after i).board.grid pos = some ⟨(tr.before i).turn.opponent, .king⟩ ∧
        inCheckOriented (tr.after i).board (tr.before i).turn.opponent pos :=
  tr.everyMoveChecksOpponent_iff_exists_king _
    (tr.kingsWellPlaced_kingPositionsFrom initial ht ha hd h0)

theorem everyMoveLeavesOwnKingSafe_kingPositionsFrom_iff_no_checked_king (tr : MoveTrace)
    (initial : Player → Pos) (ht : tr.FollowsTransitions)
    (ha : tr.MoveDestinationsAvoidKings) (hd : tr.DropMovesAreNonKings)
    (h0 : MPC.KingsWellPlaced (tr.states 0).board initial) :
    tr.EveryMoveLeavesOwnKingSafe (tr.kingPositionsFrom initial) ↔
      ∀ i : Fin tr.len, ¬ ∃ pos : Pos,
        (tr.after i).board.grid pos = some ⟨(tr.before i).turn, .king⟩ ∧
        inCheckOriented (tr.after i).board (tr.before i).turn pos :=
  tr.everyMoveLeavesOwnKingSafe_iff_no_checked_king _
    (tr.kingsWellPlaced_kingPositionsFrom initial ht ha hd h0)

end MPC.MoveTrace
