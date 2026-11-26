import MPC.Invariants.DiscHTrace
/-!
# MPC.Invariants.DiscHInvariant

`disc_H_state_total_invariant`, restated on the GameSeq-independent trace model. The earlier GameSeq statement depended on the residual axiom
`discH_state_total_boardMoveStaticEndpointActiveLowerBoundTargets_ax`, and both
were deleted. GameSeq cannot satisfy the movement rules, so the
paper's Proposition 3.8 is proved on traces instead (`MPC/Basic/DiscHTrace.lean`).

The premises are those of a periodic mutual-check trace: transitions,
owner-owned board-move sources, consistent king placement, every move leaving
the mover's king safe and checking the opponent's king, the opponent safe
before the first move, owner-oriented movement, and periodicity. No axiom
beyond Lean's standard three is used.
-/

namespace MPC

/-- Proposition 3.8 for both half-planes: on a periodic mutual-check trace, the
    total `|disc H|` (openable pieces plus checking pieces on each side of the
    line through both kings, summed over the two sides) is the same in every
    state. -/
theorem disc_H_state_total_invariant (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i j : Fin (tr.len + 1)) :
    tr.discHTotal kp i = tr.discHTotal kp j :=
  tr.discHTotal_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp i j

end MPC
