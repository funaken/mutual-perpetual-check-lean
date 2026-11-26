import MPC.Trace.PeriodicMutualCheck
import Lean
/-!
# MPC.Tests.PeriodicMutualCheck

Checks for .

- `PeriodicMutualCheck` has exactly the fields of `MutualPerpetualCheck` other than
  `dropsEmpty`, in the same order (checked on the structures' field lists).
- With drops from the hand, a `PeriodicMutualCheck` trace satisfies the drop rule,
  through `toMutualPerpetualCheck`.

No periodic mutual-check trace is constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Periodic mutual check verification must not import GameSeq"

open Lean in
run_cmd do
  let env ← getEnv
  let full := getStructureFields env `MPC.MoveTrace.MutualPerpetualCheck
  let core := getStructureFields env `MPC.MoveTrace.PeriodicMutualCheck
  unless core.toList == full.toList.filter (· != `dropsEmpty) do
    throwError
      "PeriodicMutualCheck must be MutualPerpetualCheck without dropsEmpty: {core} vs {full}"
  unless full.size == 10 && core.size == 9 do
    throwError "unexpected field counts: {full.size}, {core.size}"

namespace MPC
namespace PeriodicMutualCheckTests

open MoveTrace

-- With drops from the hand, the drop rule follows.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos) (h : tr.PeriodicMutualCheck kp)
    (hdrop : tr.DropsFromHand) : tr.DropDestinationsEmpty :=
  (h.toMutualPerpetualCheck hdrop).dropsEmpty

end PeriodicMutualCheckTests
end MPC
