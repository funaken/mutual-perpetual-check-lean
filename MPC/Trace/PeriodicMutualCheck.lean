import MPC.Invariants.DropDestinations
/-!
# MPC.Trace.PeriodicMutualCheck

The main theorem's premises without the drop rule.

`MutualPerpetualCheck` collects ten premises, one of which is
`DropDestinationsEmpty` (drops land on empty squares). The counting argument derives that rule
from `DropsFromHand` and periodicity, so the main theorem can do without it:

- `PeriodicMutualCheck`: the other nine premises of `MutualPerpetualCheck`.
- `PeriodicMutualCheck.toMutualPerpetualCheck`: with `DropsFromHand` it gives back
  `MutualPerpetualCheck`; the drop rule comes from
  `dropDestinationsEmpty_of_dropsFromHand`.
- `MutualPerpetualCheck.toPeriodicMutualCheck`: the converse forgets the drop rule.

So `PeriodicMutualCheck kp ∧ DropsFromHand` and `MutualPerpetualCheck kp ∧
DropsFromHand` are equivalent; the main theorem is restated on the first without
changing what it says. `MutualPerpetualCheck` itself is unchanged.

-/

namespace MPC
namespace MoveTrace

/-- A periodic mutual-check trace without the drop rule: the premises of
    `MutualPerpetualCheck` other than `dropsEmpty`. -/
structure PeriodicMutualCheck (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos) :
    Prop where
  transitions : tr.FollowsTransitions
  sourcesOwned : tr.BoardMoveSourcesOwned
  kingsWellPlaced : tr.KingsWellPlaced kp
  ownKingSafe : tr.EveryMoveLeavesOwnKingSafe kp
  initialOpponentSafe : tr.InitialOpponentKingSafe kp
  checks : tr.EveryMoveChecksOpponent kp
  movementRules : tr.BoardMovesFollowCanMoveToOriented
  periodic : tr.IsPeriodic
  nonempty : 0 < tr.len

/-- With drops from the hand, a periodic mutual-check trace satisfies the drop rule,
    so it is a `MutualPerpetualCheck` trace. -/
theorem PeriodicMutualCheck.toMutualPerpetualCheck {tr : MoveTrace}
    {kp : Fin (tr.len + 1) → Player → Pos} (h : tr.PeriodicMutualCheck kp)
    (hdrop : tr.DropsFromHand) : tr.MutualPerpetualCheck kp where
  transitions := h.transitions
  sourcesOwned := h.sourcesOwned
  kingsWellPlaced := h.kingsWellPlaced
  ownKingSafe := h.ownKingSafe
  initialOpponentSafe := h.initialOpponentSafe
  checks := h.checks
  movementRules := h.movementRules
  periodic := h.periodic
  dropsEmpty := tr.dropDestinationsEmpty_of_dropsFromHand h.transitions h.sourcesOwned
    (tr.boardMoveEndpointsDistinct_of_oriented h.sourcesOwned h.movementRules) hdrop h.periodic
  nonempty := h.nonempty

/-- A `MutualPerpetualCheck` trace is a periodic mutual-check trace: forget the drop
    rule. -/
theorem MutualPerpetualCheck.toPeriodicMutualCheck {tr : MoveTrace}
    {kp : Fin (tr.len + 1) → Player → Pos} (h : tr.MutualPerpetualCheck kp) :
    tr.PeriodicMutualCheck kp where
  transitions := h.transitions
  sourcesOwned := h.sourcesOwned
  kingsWellPlaced := h.kingsWellPlaced
  ownKingSafe := h.ownKingSafe
  initialOpponentSafe := h.initialOpponentSafe
  checks := h.checks
  movementRules := h.movementRules
  periodic := h.periodic
  nonempty := h.nonempty

/-- With drops from the hand, the two forms of the premises are equivalent. -/
theorem periodicMutualCheck_iff_mutualPerpetualCheck (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hdrop : tr.DropsFromHand) :
    tr.PeriodicMutualCheck kp ↔ tr.MutualPerpetualCheck kp :=
  ⟨fun h => h.toMutualPerpetualCheck hdrop, fun h => h.toPeriodicMutualCheck⟩

end MoveTrace
end MPC
