import MPC.Chess.Figure3Moves

namespace MPC.Chess.Tests

open LatticeFrame

-- Line moves and knight jumps have a step shape; other displacements do not.
example : StepShape 0 5 ∧ StepShape 3 (-3) ∧ StepShape 2 1 ∧ StepShape (-1) (-2) ∧
    ¬ StepShape (-1) 3 ∧ ¬ StepShape 3 2 := by
  norm_num [StepShape]

-- Shapes are invariant under every lattice frame.
example (F : LatticeFrame) : StepShape (F.apply (2, 1)).1 (F.apply (2, 1)).2 ∧
    ¬ StepShape (F.apply (-1, 3)).1 (F.apply (-1, 3)).2 := by
  rw [stepShape_frame, stepShape_frame]
  norm_num [StepShape]

-- Upper candidate (3,1) from K = (0,0): crossings A = (0,1) and B = (2,2) are a
-- knight's move apart, while (1,1) and (0,4), the other pair on different rays
-- of both kings, are not a move apart.
example : StepShape (2 - 0) (2 - 1) ∧ ¬ StepShape (0 - 1) (4 - 1) := by
  norm_num [StepShape]

-- Upper candidates (5,1) and (4,2): neither pair on different rays is a move apart.
example : ¬ StepShape (0 - 1) (6 - 1) ∧ ¬ StepShape (0 - 3) (1 - 3) ∧
    ¬ StepShape (0 - 2) (6 - 2) ∧ ¬ StepShape (0 - 3) (2 - 3) := by
  norm_num [StepShape]

-- The board crossings of the upper candidate (3,1) in canonical coordinates.
example (F : LatticeFrame) (K L q : Pos)
    (hL : L.toPlane = K.toPlane + F.apply (3, 1))
    (h₁ : OnRay K (F.dir .northEast) q) (h₂ : OnRay L (F.dir .northWest) q) :
    q.toPlane = K.toPlane + F.apply (2, 2) := by
  rw [crossing_northEast_northWest hL h₁ h₂]; norm_num

-- The trace interface: only the lower candidate of Figure 3 survives, with all
-- eight checking rays, without any candidate or move-shape assumption.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) :
    ∃ (c : Color) (F : LatticeFrame),
      (kp 0 c.opponent).toPlane = (kp 0 c).toPlane + F.apply (3, 1) ∧
      tr.CheckingRay (kp 0 c) c (F.dir .southEast) ∧
      tr.CheckingRay (kp 0 c.opponent) c.opponent (F.dir .south) := by
  obtain ⟨c, F, hL, hu, hv⟩ := tr.figure3_lower_candidate_of_periodic_checks kp hl hk hc hp hn
  exact ⟨c, F, hL, (hu _).mpr (by simp), (hv _).mpr (by simp)⟩

end MPC.Chess.Tests
