import MPC.Chess.CheckingRayRank

namespace MPC.Chess.Tests

-- The trace interface needs no rank, side or crossing assumption.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len)
    (c : Color) (d : RayDirection) (hr : tr.CheckingRay (kp 0 c) c d) :
    kingRayRank (kp 0 c).toPlane (kp 0 c.opponent).toPlane d ≤ 2 ∧
      ∃ side u₂ v₂, d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side ∧
        tr.CheckingRay (kp 0 c) c u₂ ∧ tr.CheckingRay (kp 0 c.opponent) c.opponent v₂ ∧
        ∃ q : Pos, OnRay (kp 0 c) u₂ q ∧ OnRay (kp 0 c.opponent) v₂ q := by
  refine ⟨tr.checkingRay_rank_le_two_of_periodic_checks kp hl hk hc hp hn c d hr, ?_⟩
  obtain ⟨side, hs⟩ := exists_mem_halfPlaneDirections
    (tr.checkingRay_offset_ne_zero_of_periodic_checks kp hl hk hc hp hn c d hr)
  obtain ⟨u₁, u₂, v₁, v₂, -, -, -, -, hu, hv, _, hsu₂, _, hsv₂, hq⟩ :=
    tr.halfPlane_checkingRays_of_periodic_checks kp hl hk hc hp hn c side d hr hs
  exact ⟨side, u₂, v₂, hs, (hu u₂ hsu₂).mpr (Or.inr rfl), (hv v₂ hsv₂).mpr (Or.inr rfl),
    hq u₂ (Or.inr rfl) v₂ (Or.inr rfl)⟩

end MPC.Chess.Tests
