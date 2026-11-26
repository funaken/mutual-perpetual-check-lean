import MPC.Trace.KingPlacementPreservation
/-!
# MPC.Trace.KingPlacementTrace

Generate king positions from initial positions and moves, independently of board
contents or proofs. Initial placement, transitions, and local conditions on the
actual before-state boards then establish placement at every state.
-/

namespace MPC.MoveTrace

/-- Neither kind of move overwrites a king on the actual before-state board.
    This condition does not refer to a supplied or generated position sequence. -/
def MoveDestinationsAvoidKings (tr : MoveTrace) : Prop :=
  ∀ i : Fin tr.len,
    match tr.moves i with
    | .boardMove _ dst _ =>
        ∀ owner, (tr.before i).board.grid dst ≠ some ⟨owner, .king⟩
    | .dropMove _ dst =>
        ∀ owner, (tr.before i).board.grid dst ≠ some ⟨owner, .king⟩

/-- Drops introduce no kings; no other drop-legality condition is asserted. -/
def DropMovesAreNonKings (tr : MoveTrace) : Prop :=
  ∀ (i : Fin tr.len) (pt : PieceType) (dst : Pos),
    tr.moves i = .dropMove pt dst → pt ≠ .king

/-- Positions computed only from the initial positions and move sequence.
    Board moves update source kings; drops leave all positions unchanged. -/
def kingPositionsFrom (tr : MoveTrace) (initial : Player → Pos) :
    Fin (tr.len + 1) → Player → Pos :=
  Fin.induction initial (fun i kp => match tr.moves i with
    | .boardMove src dst _ => kingPosAfterBoardMove kp src dst
    | .dropMove _ _ => kp)

theorem kingPositionsFrom_zero (tr : MoveTrace) (initial : Player → Pos) :
    tr.kingPositionsFrom initial 0 = initial := by
  simp [kingPositionsFrom]

theorem kingPositionsFrom_succ (tr : MoveTrace) (initial : Player → Pos)
    (i : Fin tr.len) :
    tr.kingPositionsFrom initial i.succ =
      match tr.moves i with
      | .boardMove src dst _ =>
          kingPosAfterBoardMove (tr.kingPositionsFrom initial i.castSucc) src dst
      | .dropMove _ _ => tr.kingPositionsFrom initial i.castSucc := by
  simp [kingPositionsFrom, Fin.induction_succ]

/-- Initial consistency propagates through the entire trace. After-state or
    all-state placement is not assumed; complete move legality is not claimed. -/
theorem kingsWellPlaced_kingPositionsFrom (tr : MoveTrace)
    (initial : Player → Pos)
    (ht : tr.FollowsTransitions) (ha : tr.MoveDestinationsAvoidKings)
    (hd : tr.DropMovesAreNonKings)
    (h0 : MPC.KingsWellPlaced (tr.states 0).board initial) :
    tr.KingsWellPlaced (tr.kingPositionsFrom initial) := by
  intro j
  induction j using Fin.induction with
  | zero => simpa only [kingPositionsFrom_zero] using h0
  | succ i ih =>
    change MPC.KingsWellPlaced (tr.after i).board
      (tr.kingPositionsFrom initial i.succ)
    rw [ht i, kingPositionsFrom_succ]
    cases hm : tr.moves i with
    | boardMove src dst promote =>
      have havoid := ha i
      rw [hm] at havoid
      apply ih.applyMove_boardMove
      intro owner heq
      apply havoid owner
      rw [heq]
      exact ih.king_present owner
    | dropMove pt dst =>
      have havoid := ha i
      rw [hm] at havoid
      apply ih.applyMove_dropMove pt dst (hd i pt dst hm)
      intro owner heq
      apply havoid owner
      rw [heq]
      exact ih.king_present owner

/-- Any placement consistent with the trace equals the generated sequence.
    Uniqueness of a sequence does not mean its positions are constant in time. -/
theorem kingPositionsFrom_eq_of_kingsWellPlaced (tr : MoveTrace)
    (initial : Player → Pos)
    (ht : tr.FollowsTransitions) (ha : tr.MoveDestinationsAvoidKings)
    (hd : tr.DropMovesAreNonKings)
    (h0 : MPC.KingsWellPlaced (tr.states 0).board initial)
    (other : Fin (tr.len + 1) → Player → Pos)
    (ho : tr.KingsWellPlaced other) :
    tr.kingPositionsFrom initial = other :=
  (tr.kingsWellPlaced_kingPositionsFrom initial ht ha hd h0).positions_unique ho

end MPC.MoveTrace
