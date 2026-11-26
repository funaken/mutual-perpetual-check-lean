import MPC.Chess.Figure3Candidates

namespace MPC.Chess.Tests

-- The lower candidate of Figure 3: with kings at (0,3) and (3,4), both
-- half-planes have their four crossings on the board, using all eight rows.
example : OnRay (0, 3) .north (0, 4) ∧ OnRay (3, 4) .west (0, 4) ∧
    OnRay (0, 3) .northEast (1, 4) ∧ OnRay (3, 4) .west (1, 4) ∧
    OnRay (0, 3) .north (0, 7) ∧ OnRay (3, 4) .northWest (0, 7) ∧
    OnRay (0, 3) .northEast (2, 5) ∧ OnRay (3, 4) .northWest (2, 5) ∧
    OnRay (0, 3) .east (3, 3) ∧ OnRay (3, 4) .south (3, 3) ∧
    OnRay (0, 3) .east (2, 3) ∧ OnRay (3, 4) .southWest (2, 3) ∧
    OnRay (0, 3) .southEast (3, 0) ∧ OnRay (3, 4) .south (3, 0) ∧
    OnRay (0, 3) .southEast (1, 2) ∧ OnRay (3, 4) .southWest (1, 2) := by decide

-- For `(5, 1)` the upper crossing `K + (0, 6)` and the lower crossing
-- `K + (5, -5)` need eleven rows; one half-plane is all that fits.
example : (∃ q : Pos, OnRay (0, 1) .north q ∧ OnRay (5, 2) .northWest q) ∧
    ¬ ∃ q : Pos, OnRay (0, 1) .southEast q ∧ OnRay (5, 2) .south q := by decide

-- The same for `(4, 2)`, which needs ten rows.
example : (∃ q : Pos, OnRay (0, 1) .north q ∧ OnRay (4, 3) .northWest q) ∧
    ¬ ∃ q : Pos, OnRay (0, 1) .southEast q ∧ OnRay (4, 3) .south q := by decide

-- The trace interface: from the trace hypotheses alone, every checking ray of
-- either king is one of at most four framed directions, and the kings are in
-- one of the Figure 3 relative positions.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) :
    ∃ (c : Color) (F : LatticeFrame) (a b : ℤ),
      ((a = 3 ∧ b = 1) ∨ (a = 5 ∧ b = 1) ∨ (a = 4 ∧ b = 2)) ∧
      (kp 0 c.opponent).toPlane = (kp 0 c).toPlane + F.apply ((a : ℚ), (b : ℚ)) ∧
      ∀ d, tr.CheckingRay (kp 0 c) c d →
        d = F.dir .northEast ∨ d = F.dir .north ∨ d = F.dir .east ∨ d = F.dir .southEast := by
  obtain ⟨c, F, a, b, both, hab, -, hL, hu, -⟩ :=
    tr.figure3_candidates_of_periodic_checks kp hl hk hc hp hn
  refine ⟨c, F, a, b, hab, hL, fun d h => ?_⟩
  rcases (hu d).mp h with h | h | ⟨-, h | h⟩
  exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]

end MPC.Chess.Tests
