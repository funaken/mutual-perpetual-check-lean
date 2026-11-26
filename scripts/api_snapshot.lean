import MPC.Verification
import MPC.Legacy
import Lean

/-! Export types and transitive axiom dependencies for regression comparison.
    MPC_API_OUTPUT chooses the output path; no proof terms are changed. -/
open Lean in
run_cmd do
  let some output ← IO.getEnv "MPC_API_OUTPUT"
    | throwError "Set MPC_API_OUTPUT to a writable JSONL output path"
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    if (`MPC).isPrefixOf n && !n.isInternal then
      let axioms ← collectAxioms n
      rows := rows.push <| (Json.arr #[toJson n.toString, toJson (toString (repr ci.type)),
        toJson ((axioms.toList.map Name.toString).mergeSort)]).compress
  rows := rows.qsort (· < ·)
  IO.FS.writeFile output (String.intercalate "\n" rows.toList ++ "\n")
