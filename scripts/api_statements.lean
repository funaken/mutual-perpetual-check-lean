import MPC.Verification
import MPC.Legacy
import Lean

/-! Print the statements of the declarations named in the file `MPC_NAMES`
    (one per line) to `MPC_PP_OUTPUT`, as `name<TAB>type` lines.

    Notation, structure-instance syntax and Unicode `fun` are turned off and
    names are printed in full, so that two Lean toolchains print the same
    statement the same way. Implicit arguments, instances and proofs are hidden
    as usual. Used with `scripts/compare_api_snapshots.py`; see
    `docs/validation/toolchain-migration-4.36.md`. -/
open Lean Meta in
set_option pp.notation false in
set_option pp.fullNames true in
set_option pp.unicode.fun false in
set_option pp.structureInstances false in
set_option format.width 100000 in
#eval show MetaM Unit from do
  let some path ← IO.getEnv "MPC_NAMES" | throwError "Set MPC_NAMES to a file of names"
  let some out ← IO.getEnv "MPC_PP_OUTPUT" | throwError "Set MPC_PP_OUTPUT to an output path"
  let names := ((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "")
  let mut lines : Array String := #[]
  for n in names do
    match (← getEnv).find? n.toName with
    | some ci =>
      let f ← ppExpr ci.type
      lines := lines.push (n ++ "\t" ++ (toString f).replace "\n" " ")
    | none => lines := lines.push (n ++ "\t<missing>")
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
