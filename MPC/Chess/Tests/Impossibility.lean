import MPC.Chess.Impossibility

namespace MPC.Chess.Tests

-- The lower candidate of Figure 3 with kings at K = (0,3) and L = (3,4). The
-- ray LC (south from L) meets the rays of K at (3,3) and at C = (3,0), the last
-- square of the board.
example : OnRay (3, 4) .south (3, 3) ∧ OnRay (0, 3) .east (3, 3) ∧
    OnRay (3, 4) .south (3, 0) ∧ OnRay (0, 3) .southEast (3, 0) ∧
    ¬ ∃ q : Pos, OnRay (3, 4) .south q ∧ OnRay (0, 3) .north q := by decide

-- From C = (3,0) no crossing on other rays of both kings is a line move or a
-- knight jump away: (0,4), (1,4), (0,7), (2,5) and (2,3).
example : ¬ StepShape (0 - 3) (4 - 0) ∧ ¬ StepShape (1 - 3) (4 - 0) ∧
    ¬ StepShape (0 - 3) (7 - 0) ∧ ¬ StepShape (2 - 3) (5 - 0) ∧
    ¬ StepShape (2 - 3) (3 - 0) := by
  norm_num [StepShape]

-- Other crossings of the lower candidate are moves apart, so the argument needs
-- the checker on C: (2,3) to (1,4) is diagonal and (0,4) to (2,3) a knight jump.
example : StepShape (1 - 2) (4 - 3) ∧ StepShape (2 - 0) (3 - 4) := by
  norm_num [StepShape]

private def kingsOnly : Board := fun q =>
  if q = (0, 3) then some ⟨.white, .king⟩
  else if q = (3, 4) then some ⟨.black, .king⟩ else none

private def kingsAt : Color → Pos
  | .white => (0, 3)
  | .black => (3, 4)

-- The positive length cannot be dropped: the empty trace satisfies every other
-- premise of the main theorem.
example : ∃ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos),
    tr.FollowsLegalMoves ∧ tr.KingsWellPlaced kp ∧ tr.EveryMoveChecksOpponent kp ∧
      tr.BoardTurnPeriodic ∧ tr.len = 0 := by
  refine ⟨.empty ⟨kingsOnly, .white, {}, none⟩, fun _ => kingsAt, fun i => Fin.elim0 i, ?_,
    fun i => Fin.elim0 i, ⟨rfl, rfl⟩, rfl⟩
  intro _
  show MPC.Chess.KingsWellPlaced kingsOnly kingsAt
  unfold MPC.Chess.KingsWellPlaced
  decide

-- The main theorem: no positive-length legal sequence checks with every move
-- and returns to its initial board and side to move.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic) : tr.len = 0 := by
  by_contra h
  exact mutual_perpetual_check_impossible ⟨tr, kp, Nat.pos_of_ne_zero h, hl, hk, hc, hp⟩

end MPC.Chess.Tests
