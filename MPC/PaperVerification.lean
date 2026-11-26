import MPC.Main
import Lean

/-! Publication entry point: the exact theorem statement and its trust boundary.
    Importing this module does not import legacy APIs or regression examples. -/
namespace MPC

example : ¬ ∃ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos),
    tr.PeriodicMutualCheck kp ∧ tr.DropsFromHand ∧ tr.InitialPieceCountsAtMostTwo :=
  mutual_perpetual_check_impossible

end MPC

/-- info: 'MPC.mutual_perpetual_check_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.mutual_perpetual_check_impossible

open Lean in
run_cmd do
  let env ← getEnv
  for n in [`MPC.GameSeq, `MPC.canMoveTo, `MPC.attacks, `MPC.inCheck,
      `MPC.MoveTrace.BoardMovesFollowCanMoveTo] do
    if env.contains n then
      throwError "Publication proof imports historical declaration {n}"
  for n in [`MPC.mem_slidePath_iff_of_exact_steps,
      `MPC.MoveTrace.discHCount_succ_eq, `MPC.MoveTrace.kingPos_eq_of_periodic,
      `MPC.MoveTrace.openable_destination_lines_cyclic_of_periodic,
      `MPC.MoveTrace.checker_off_kingLine_of_periodic,
      `MPC.MoveTrace.discHCount_eq_of_periodic,
      `MPC.vecKey_of_mul, `MPC.vecKey_lt_of_comb,
      `MPC.MoveTrace.anglePotential,
      `MPC.MoveTrace.discoveredCheckByEachSide_of_mutualPerpetualCheck,
      `MPC.MoveTrace.not_openableMove_silver_of_periodic,
      `MPC.MoveTrace.not_openableMove_bishopHorse_of_periodic] do
    unless env.contains n do
      throwError "Manuscript references missing declaration {n}"
    for a in ← collectAxioms n do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "{n} uses unexpected axiom {a}"
