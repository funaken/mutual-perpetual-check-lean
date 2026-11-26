import MPC.Main
import Lean
/-!
# MPC.Tests.MainImport

`MPC.Main` (the main theorem) does not import the old GameSeq side.
This module imports only `MPC.Main`, so its environment holds exactly what the
main theorem's file brings in; the check fails if `MPC.GameSeq` is among it.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "MPC.Main must not import GameSeq"
  for n in [`MPC.canMoveTo, `MPC.attacks, `MPC.inCheck, `MPC.isDirectCheck,
      `MPC.isDiscoveredCheck, `MPC.MoveTrace.BoardMovesFollowCanMoveTo] do
    if (← getEnv).contains n then
      throwError "MPC.Main must not import legacy declaration {n}"
