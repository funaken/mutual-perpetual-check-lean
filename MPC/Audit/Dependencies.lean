import MPC.Main
import MPC.Legacy
import Lean
/-!
# MPC.Verification

主定理・中間定理の公理依存と証明経路、および具体例の回帰検証。
`#guard_msgs`の直前にある期待出力コメントは検証コードの一部である。

独自公理は0件。主定理の仮定は`PeriodicMutualCheck`、`DropsFromHand`、
`InitialPieceCountsAtMostTwo`であり、命題4.1や全状態の駒数上限を仮定しない。
半平面不変量を使う駒種別の分岐が角・馬であることも依存経路で検査する。
-/

-- 最終定理: `MoveTrace` で述べ、Lean 標準公理のみに依存する。
/-- info: 'MPC.mutual_perpetual_check_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.mutual_perpetual_check_impossible
-- 強い形: `PieceCountsAtMostTwo` を前提にとる。
/-- info: 'MPC.mutual_perpetual_check_impossible_of_pieceCounts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.mutual_perpetual_check_impossible_of_pieceCounts

-- 主定理の型と証明が `GameSeq` に依存しないこと、型が命題 4.1 と駒の枚数 を
-- 前提に含まず証明がそれぞれの定理を使うこと、および命題 3.8 (`discHCount_eq_of_periodic`)
-- を使う駒種の除外が角・馬だけであることを検査する。
open Lean in
run_cmd do
  let env ← getEnv
  -- `root` から到達できる定数の集合。反復の上限に達したら (集合が不完全なので) 失敗する。
  let reachAux (root : Name) : NameSet × Bool := Id.run do
    let mut seen : NameSet := {}
    let mut stack := #[root]
    for _ in [0:1000000] do
      match stack.back? with
      | none => break
      | some n =>
        stack := stack.pop
        unless seen.contains n do
          seen := seen.insert n
          if let some c := env.find? n then
            for m in c.getUsedConstantsAsSet do
              unless seen.contains m do stack := stack.push m
    return (seen, stack.isEmpty)
  let reach (root : Name) : Elab.Command.CommandElabM NameSet := do
    let (seen, complete) := reachAux root
    unless complete do throwError "reachability from {root} did not finish"
    return seen
  -- 旧 `GameSeq` は削除済みで、環境にない。
  if env.contains `MPC.GameSeq then
    throwError "MPC.GameSeq must not exist (#256)"
  let main := `MPC.mutual_perpetual_check_impossible
  let some c := env.find? main | throwError "{main} is missing"
  if c.type.getUsedConstants.any (`MPC.GameSeq).isPrefixOf then
    throwError "the type of {main} mentions GameSeq"
  let mainReach ← reach main
  if mainReach.toList.any (`MPC.GameSeq).isPrefixOf then
    throwError "the proof of {main} uses GameSeq"
  if c.type.getUsedConstants.contains `MPC.MoveTrace.DiscoveredCheckByEachSide then
    throwError "the type of {main} assumes Proposition 4.1 (DiscoveredCheckByEachSide)"
  unless mainReach.contains `MPC.MoveTrace.discoveredCheckByEachSide_of_mutualPerpetualCheck do
    throwError "the proof of {main} does not use Proposition 4.1's proof (#82)"
  if c.type.getUsedConstants.contains `MPC.MoveTrace.PieceCountsAtMostTwo then
    throwError "the type of {main} assumes PieceCountsAtMostTwo"
  -- the drop rule is derived, so the type uses `PeriodicMutualCheck`.
  if c.type.getUsedConstants.contains `MPC.MoveTrace.MutualPerpetualCheck then
    throwError "the type of {main} assumes MutualPerpetualCheck (with the drop rule)"
  if c.type.getUsedConstants.contains `MPC.MoveTrace.DropDestinationsEmpty then
    throwError "the type of {main} assumes DropDestinationsEmpty"
  unless mainReach.contains `MPC.MoveTrace.dropDestinationsEmpty_of_dropsFromHand do
    throwError "the proof of {main} does not derive the drop rule (#264)"
  unless mainReach.contains `MPC.MoveTrace.pieceCountsAtMostTwo_of_dropsFromHand do
    throwError "the proof of {main} does not derive the piece counts (#255)"
  let prop38 := `MPC.MoveTrace.discHCount_eq_of_periodic
  for (r, uses) in [(`MPC.MoveTrace.not_openableMove_forward_of_periodic, false),
      (`MPC.MoveTrace.not_openableMove_goldType_of_periodic, false),
      (`MPC.MoveTrace.not_openableMove_silver_of_periodic, false),
      (`MPC.MoveTrace.not_openableMove_rookDragon_of_periodic, false),
      (`MPC.MoveTrace.not_openableMove_bishopHorse_of_periodic, true)] do
    if (← reach r).contains prop38 != uses then
      throwError "{r}: use of Proposition 3.8 differs from the paper (expected {uses})"

-- 中間定理と基礎APIの依存検査
/-- info: 'MPC.MoveTrace.turn_after_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.turn_after_move
/-- info: 'MPC.MoveTrace.boardMove_grid_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMove_grid_src
/-- info: 'MPC.MoveTrace.boardMove_grid_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMove_grid_dst
/-- info: 'MPC.MoveTrace.boardMove_grid_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMove_grid_other
/-- info: 'MPC.MoveTrace.dropMove_grid_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.dropMove_grid_dst
/-- info: 'MPC.MoveTrace.dropMove_grid_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.dropMove_grid_other
/-- info: 'MPC.MoveTrace.single_followsTransitions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.single_followsTransitions
-- owner-oriented movement without changing the legacy predicate.
/-- info: 'MPC.canMoveToOriented_pawn_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.canMoveToOriented_pawn_iff
/-- info: 'MPC.canMoveToOriented_not_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.canMoveToOriented_not_self
/-- info: 'MPC.canMoveToOriented_iff_canMoveTo_of_symmetric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.canMoveToOriented_iff_canMoveTo_of_symmetric
/-- info: 'MPC.MoveTrace.boardMoveEndpointsDistinct_of_oriented' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMoveEndpointsDistinct_of_oriented
-- exact slide-path membership and clearance .
/-- info: 'MPC.slideSteps_le_eight_of_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.slideSteps_le_eight_of_endpoints
/-- info: 'MPC.mem_slidePath_iff_of_exact_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.mem_slidePath_iff_of_exact_steps
/-- info: 'MPC.slidePoint_onBoard_of_exact_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.slidePoint_onBoard_of_exact_steps
/-- info: 'MPC.pathClear_iff_of_exact_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.pathClear_iff_of_exact_steps
-- owner-oriented attacks/checks and explicit preservation conditions.
/-- info: 'MPC.pathClear_mono_of_empty_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.pathClear_mono_of_empty_preserved
/-- info: 'MPC.attacksOriented_not_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.attacksOriented_not_self
/-- info: 'MPC.attacksOriented_iff_attacks_of_symmetric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.attacksOriented_iff_attacks_of_symmetric
/-- info: 'MPC.attacksOriented_mono_of_empty_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.attacksOriented_mono_of_empty_preserved
/-- info: 'MPC.inCheckOriented_mono_of_checkers_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.inCheckOriented_mono_of_checkers_preserved
/-- info: 'MPC.inCheckOriented_iff_inCheck_of_symmetric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.inCheckOriented_iff_inCheck_of_symmetric
-- exact king placement with state-indexed, potentially moving positions.
/-- info: 'MPC.KingsWellPlaced.king_present' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.KingsWellPlaced.king_present
/-- info: 'MPC.KingsWellPlaced.positions_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.KingsWellPlaced.positions_injective
/-- info: 'MPC.KingsWellPlaced.positions_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms MPC.KingsWellPlaced.positions_unique
/-- info: 'MPC.KingsWellPlaced.inCheckOriented_iff_exists_king' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.KingsWellPlaced.inCheckOriented_iff_exists_king
/-- info: 'MPC.MoveTrace.KingsWellPlaced.positions_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.KingsWellPlaced.positions_unique
/-- info: 'MPC.MoveTrace.kingPos_after_boardMove_king' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPos_after_boardMove_king
/-- info: 'MPC.MoveTrace.kingPos_after_boardMove_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPos_after_boardMove_of_ne
/-- info: 'MPC.MoveTrace.kingPos_after_dropMove_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPos_after_dropMove_of_ne
-- derive after-state king placement under local sufficient conditions.
/-- info: 'MPC.PieceType.promote_eq_king_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.PieceType.promote_eq_king_iff
/-- info: 'MPC.KingsWellPlaced.applyMove_boardMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.KingsWellPlaced.applyMove_boardMove
/-- info: 'MPC.KingsWellPlaced.applyMove_dropMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.KingsWellPlaced.applyMove_dropMove
-- generate king positions and derive placement at every trace state.
/-- info: 'MPC.MoveTrace.kingPositionsFrom_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPositionsFrom_zero
/-- info: 'MPC.MoveTrace.kingPositionsFrom_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPositionsFrom_succ
/-- info: 'MPC.MoveTrace.kingsWellPlaced_kingPositionsFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingsWellPlaced_kingPositionsFrom
/-- info: 'MPC.MoveTrace.kingPositionsFrom_eq_of_kingsWellPlaced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPositionsFrom_eq_of_kingsWellPlaced
-- checking and self-safety at state-indexed, actual king positions.
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_iff_after_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_iff_after_turn
/-- info: 'MPC.MoveTrace.everyMoveLeavesOwnKingSafe_iff_after_opponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveLeavesOwnKingSafe_iff_after_opponent
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_iff_exists_king' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_iff_exists_king
/-- info: 'MPC.MoveTrace.everyMoveLeavesOwnKingSafe_iff_no_checked_king' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveLeavesOwnKingSafe_iff_no_checked_king
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_kingPositionsFrom_iff_exists_king' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_kingPositionsFrom_iff_exists_king
/-- info: 'MPC.MoveTrace.everyMoveLeavesOwnKingSafe_kingPositionsFrom_iff_no_checked_king' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveLeavesOwnKingSafe_kingPositionsFrom_iff_no_checked_king
-- inclusive destination/other-position decomposition of check witnesses.
/-- info: 'MPC.inCheckOriented_of_destinationChecker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.inCheckOriented_of_destinationChecker
/-- info: 'MPC.inCheckOriented_of_otherChecker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.inCheckOriented_of_otherChecker
/-- info: 'MPC.inCheckOriented_iff_destination_or_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.inCheckOriented_iff_destination_or_other
/-- info: 'MPC.hasOtherCheckerOriented_of_inCheck_of_not_destination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.hasOtherCheckerOriented_of_inCheck_of_not_destination
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_iff_destination_or_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_iff_destination_or_other
-- one-update source unblocking, independent of global immovability.
/-- info: 'MPC.applyMove_boardMove_other_piece_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_boardMove_other_piece_before
/-- info: 'MPC.applyMove_boardMove_new_attack_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_boardMove_new_attack_path
/-- info: 'MPC.applyMove_boardMove_new_attack_exact_slide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_boardMove_new_attack_exact_slide
/-- info: 'MPC.applyMove_boardMove_otherChecker_source_unblocking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_boardMove_otherChecker_source_unblocking
/-- info: 'MPC.MoveTrace.boardMove_otherChecker_source_unblocking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMove_otherChecker_source_unblocking
-- drop check origin at fixed targets, without global immovability.
/-- info: 'MPC.applyMove_dropMove_pathClear_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_dropMove_pathClear_before
/-- info: 'MPC.applyMove_dropMove_attacksOriented_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_dropMove_attacksOriented_before
/-- info: 'MPC.applyMove_dropMove_otherChecker_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_dropMove_otherChecker_before
/-- info: 'MPC.applyMove_dropMove_not_otherChecker_of_not_inCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_dropMove_not_otherChecker_of_not_inCheck
/-- info: 'MPC.applyMove_dropMove_inCheck_iff_destinationChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_dropMove_inCheck_iff_destinationChecker
/-- info: 'MPC.MoveTrace.dropMove_inCheck_iff_destinationChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.dropMove_inCheck_iff_destinationChecker
-- combined destination/unblocked check origin for both move kinds.
/-- info: 'MPC.hasOtherCheckerOriented_of_unblockedChecker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.hasOtherCheckerOriented_of_unblockedChecker
/-- info: 'MPC.applyMove_otherChecker_iff_unblockedChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_otherChecker_iff_unblockedChecker
/-- info: 'MPC.applyMove_inCheck_iff_destination_or_unblocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_inCheck_iff_destination_or_unblocked
/-- info: 'MPC.MoveTrace.inCheck_iff_destination_or_unblocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.inCheck_iff_destination_or_unblocked
/-- info: 'MPC.MoveTrace.sourcePresent_of_boardMoveSourcesOwned' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.MoveTrace.sourcePresent_of_boardMoveSourcesOwned
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_iff_destination_or_unblocked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_iff_destination_or_unblocked
-- trace check-origin premises derived from placement and safety.
/-- info: 'MPC.MoveTrace.opponentKingPos_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.opponentKingPos_succ_eq
/-- info: 'MPC.MoveTrace.everyStateOpponentSafe_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyStateOpponentSafe_iff
/-- info: 'MPC.MoveTrace.before_opponent_not_inCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.before_opponent_not_inCheck
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_kingPositionsFrom_iff_destination_or_unblocked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_kingPositionsFrom_iff_destination_or_unblocked
-- oriented check origin against the legacy direct/discovered checks.
/-- info: 'MPC.canMoveTo_owner_irrelevant_of_ne_lance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.canMoveTo_owner_irrelevant_of_ne_lance
/-- info: 'MPC.attacksOriented_iff_attacks_of_legacyCompatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.attacksOriented_iff_attacks_of_legacyCompatible
/-- info: 'MPC.applyMove_isDirectCheck_iff_destinationChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_isDirectCheck_iff_destinationChecker
/-- info: 'MPC.applyMove_isDiscoveredCheck_iff_unblockedChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_isDiscoveredCheck_iff_unblockedChecker
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_iff_legacy_direct_or_discovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_iff_legacy_direct_or_discovered
-- history-based immovable pieces, glare, Lemma 2.4, and drops glaring.
/-- info: 'MPC.MoveTrace.immovableAt_grid_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.immovableAt_grid_eq
/-- info: 'MPC.MoveTrace.glaresAtEnemyKing_of_attacks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.glaresAtEnemyKing_of_attacks
/-- info: 'MPC.MoveTrace.glaresAtEnemyKing_of_destinationChecker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.glaresAtEnemyKing_of_destinationChecker
/-- info: 'MPC.MoveTrace.everyMoveChecksOpponent_glares_or_unblocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.everyMoveChecksOpponent_glares_or_unblocked
/-- info: 'MPC.MoveTrace.dropMove_glares_of_everyMoveChecksOpponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.dropMove_glares_of_everyMoveChecksOpponent
-- Lemma 2.5 (moving a glaring piece is not a discovered check), direct checks, and Lemma 2.6.
/-- info: 'MPC.attacksOriented_of_pathClear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.attacksOriented_of_pathClear
/-- info: 'MPC.mem_slidePath_of_mem_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.mem_slidePath_of_mem_tail
/-- info: 'MPC.applyMove_boardMove_pathClear_source_of_unblockedChecker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_boardMove_pathClear_source_of_unblockedChecker
/-- info: 'MPC.applyMove_boardMove_not_unblockedChecker_of_attacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_boardMove_not_unblockedChecker_of_attacks
/-- info: 'MPC.MoveTrace.not_unblockedChecker_of_source_glares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_unblockedChecker_of_source_glares
/-- info: 'MPC.MoveTrace.destinationChecker_of_source_glares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destinationChecker_of_source_glares
/-- info: 'MPC.MoveTrace.destination_glares_of_source_glares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_glares_of_source_glares
-- Proposition 2.2's per-move steps (king moves are discovered checks; aligned before, not after).
/-- info: 'MPC.not_isAligned_of_step_off_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.not_isAligned_of_step_off_line
/-- info: 'MPC.MoveTrace.kingPos_succ_of_boardMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPos_succ_of_boardMove
/-- info: 'MPC.MoveTrace.kingPos_succ_of_dropMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPos_succ_of_dropMove
/-- info: 'MPC.MoveTrace.kings_not_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kings_not_adjacent
/-- info: 'MPC.MoveTrace.kingMove_unblockedChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingMove_unblockedChecker
/-- info: 'MPC.MoveTrace.kingMove_aligned_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingMove_aligned_before
/-- info: 'MPC.MoveTrace.kingMove_not_aligned_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingMove_not_aligned_after
-- Proposition 2.2 completed (alignment is only lost; in periodic traces kings never move).
/-- info: 'MPC.Pos.isAligned_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Pos.isAligned_comm
/-- info: 'MPC.MoveTrace.kingPos_succ_of_not_kingMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPos_succ_of_not_kingMove
/-- info: 'MPC.MoveTrace.boardMove_dst_ne_kingPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMove_dst_ne_kingPos
/-- info: 'MPC.MoveTrace.dropMove_dst_ne_kingPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.dropMove_dst_ne_kingPos
/-- info: 'MPC.MoveTrace.kingsAligned_castSucc_of_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingsAligned_castSucc_of_succ
/-- info: 'MPC.MoveTrace.kingsAligned_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingsAligned_of_le
/-- info: 'MPC.MoveTrace.IsPeriodic.kingPos_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.IsPeriodic.kingPos_last
/-- info: 'MPC.MoveTrace.not_kingMoveAt_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_kingMoveAt_of_periodic
/-- info: 'MPC.MoveTrace.kingPos_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPos_eq_of_periodic
/-- info: 'MPC.MoveTrace.immovableAt_kingPos_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.immovableAt_kingPos_of_periodic
-- Lemmas 2.8/2.9 by counting non-glaring squares (periodic traces).
/-- info: 'MPC.MoveTrace.mem_nonGlaringSquares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_nonGlaringSquares
/-- info: 'MPC.MoveTrace.glaresAtEnemyKing_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.glaresAtEnemyKing_congr
/-- info: 'MPC.MoveTrace.nonGlaringSquares_card_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquares_card_succ_le
/-- info: 'MPC.MoveTrace.nonGlaringSquares_card_succ_lt_of_glares_destination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquares_card_succ_lt_of_glares_destination
/-- info: 'MPC.MoveTrace.nonGlaringSquares_card_succ_lt_of_occupied_destination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquares_card_succ_lt_of_occupied_destination
/-- info: 'MPC.MoveTrace.nonGlaringSquares_card_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquares_card_eq_of_periodic
/-- info: 'MPC.MoveTrace.glares_source_of_glares_destination_of_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.glares_source_of_glares_destination_of_periodic
/-- info: 'MPC.MoveTrace.glares_destination_of_occupied_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.glares_destination_of_occupied_of_periodic
/-- info: 'MPC.MoveTrace.glares_destination_iff_source_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.glares_destination_iff_source_of_periodic
-- Proposition 3.3 / Corollary 3.4 in a linear-interval form.
/-- info: 'MPC.stepAttack_of_attacks_of_blocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.stepAttack_of_attacks_of_blocked
/-- info: 'MPC.MoveTrace.glaringDestinationsCheck_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.glaringDestinationsCheck_of_periodic
/-- info: 'MPC.MoveTrace.unblockedChecker_of_not_glares_source_of_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.unblockedChecker_of_not_glares_source_of_periodic
/-- info: 'MPC.MoveTrace.grid_eq_of_glares_through_occupied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.grid_eq_of_glares_through_occupied
/-- info: 'MPC.MoveTrace.openable_glaring_line_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_glaring_line_of_periodic
/-- info: 'MPC.MoveTrace.destination_on_checker_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_on_checker_line
/-- info: 'MPC.MoveTrace.openable_destination_lines_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_destination_lines_of_periodic
-- Proposition 3.3 / Corollary 3.4 completed across the period.
/-- info: 'MPC.cyclicBetween_self_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.cyclicBetween_self_left
/-- info: 'MPC.cyclicBetween_iff_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.cyclicBetween_iff_of_le
/-- info: 'MPC.Move.touches_destination' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Move.touches_destination
/-- info: 'MPC.MoveTrace.grid_eq_of_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.grid_eq_of_untouched
/-- info: 'MPC.MoveTrace.destination_piece_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_piece_owner
/-- info: 'MPC.MoveTrace.not_stepAttack_of_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_stepAttack_of_before
/-- info: 'MPC.MoveTrace.departure_of_not_glares_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.departure_of_not_glares_of_periodic
/-- info: 'MPC.MoveTrace.openable_glaring_line_cyclic_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_glaring_line_cyclic_of_periodic
/-- info: 'MPC.MoveTrace.openable_destination_lines_cyclic_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_destination_lines_cyclic_of_periodic
-- Proposition 3.5 (openable pieces never move onto the line through both kings).
/-- info: 'MPC.Geometry.collinear_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Geometry.collinear_swap
/-- info: 'MPC.stepDir_unit_or_knight' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.stepDir_unit_or_knight
/-- info: 'MPC.exists_line_param_of_collinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.exists_line_param_of_collinear
/-- info: 'MPC.mem_slidePath_of_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.mem_slidePath_of_between
/-- info: 'MPC.cyclicBetween_self_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.cyclicBetween_self_right
/-- info: 'MPC.MoveTrace.inCheck_before_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.inCheck_before_of_periodic
/-- info: 'MPC.MoveTrace.openable_destination_off_kingLine_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_destination_off_kingLine_of_periodic
-- Proposition 3.6 (no checking piece on the line through both kings).
/-- info: 'MPC.collinear_of_line_params' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.collinear_of_line_params
/-- info: 'MPC.MoveTrace.mem_occupiedSquares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_occupiedSquares
/-- info: 'MPC.MoveTrace.occupiedSquares_card_succ_lt_of_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.occupiedSquares_card_succ_lt_of_capture
/-- info: 'MPC.MoveTrace.checkerOnKingLine_succ_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.checkerOnKingLine_succ_of_periodic
/-- info: 'MPC.MoveTrace.checker_off_kingLine_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.checker_off_kingLine_of_periodic
-- half-planes (Definition 3.7) and checkers: no double check, the sides of replies and discovered checkers.
/-- info: 'MPC.lineSide_eq_zero_iff_collinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.lineSide_eq_zero_iff_collinear
/-- info: 'MPC.lineSide_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.lineSide_left
/-- info: 'MPC.lineSide_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.lineSide_right
/-- info: 'MPC.lineSide_affine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.lineSide_affine
/-- info: 'MPC.lineSide_pos_iff_of_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.lineSide_pos_iff_of_between
/-- info: 'MPC.same_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.same_ray
/-- info: 'MPC.MoveTrace.checker_unique_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.checker_unique_of_periodic
/-- info: 'MPC.MoveTrace.destination_side_of_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_side_of_checker
/-- info: 'MPC.MoveTrace.unblockedChecker_side_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.unblockedChecker_side_of_periodic
/-- info: 'MPC.MoveTrace.lineSide_ne_zero_of_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.lineSide_ne_zero_of_checker
-- Proposition 3.8 (|disc H| is the same in every state, on each half-plane).
/-- info: 'MPC.MoveTrace.mem_openableSquares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_openableSquares
/-- info: 'MPC.MoveTrace.mem_checkerSquares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_checkerSquares
/-- info: 'MPC.MoveTrace.checkerSquares_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.checkerSquares_card_eq
/-- info: 'MPC.MoveTrace.card_move_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.card_move_eq
/-- info: 'MPC.MoveTrace.discHCount_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.discHCount_succ_eq
/-- info: 'MPC.MoveTrace.discHCount_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.discHCount_eq_of_periodic
/-- info: 'MPC.MoveTrace.discHTotal_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.discHTotal_eq_of_periodic
-- `disc_H_state_total_invariant` restated on traces; the residual axiom and its GameSeq consumers are deleted.
/-- info: 'MPC.disc_H_state_total_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.disc_H_state_total_invariant
-- the main theorem's premises on traces and the proof skeleton.
/-- info: 'MPC.MoveTrace.openableMove_of_unblockedChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openableMove_of_unblockedChecker
/-- info: 'MPC.MoveTrace.exists_openableMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.exists_openableMove
/-- info: 'MPC.MoveTrace.not_openableMove_king' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_openableMove_king
/-- info: 'MPC.MoveTrace.false_of_no_openableMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.false_of_no_openableMove
-- non-glaring pieces keep their kind (periodic traces).
/-- info: 'MPC.Piece.afterMove_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Piece.afterMove_false
/-- info: 'MPC.PieceType.promote_promote' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.PieceType.promote_promote
/-- info: 'MPC.PieceType.promote_ne_of_promote_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.PieceType.promote_ne_of_promote_ne
/-- info: 'MPC.Piece.afterMove_eq_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Piece.afterMove_eq_self
/-- info: 'MPC.Piece.eq_of_afterMove_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Piece.eq_of_afterMove_eq
/-- info: 'MPC.MoveTrace.boardMove_grid_dst_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMove_grid_dst_of_some
/-- info: 'MPC.MoveTrace.mem_nonGlaringSquaresOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_nonGlaringSquaresOf
/-- info: 'MPC.MoveTrace.nonGlaringSquaresOf_card_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquaresOf_card_succ_le
/-- info: 'MPC.MoveTrace.nonGlaringSquaresOf_card_succ_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquaresOf_card_succ_lt
/-- info: 'MPC.MoveTrace.count_eq_initial_of_step_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.count_eq_initial_of_step_le
/-- info: 'MPC.MoveTrace.afterMove_eq_of_not_glares_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.afterMove_eq_of_not_glares_of_periodic
/-- info: 'MPC.MoveTrace.boardMove_grid_dst_eq_of_not_glares_of_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMove_grid_dst_eq_of_not_glares_of_periodic
/-- info: 'MPC.MoveTrace.nonGlaringSquaresOf_card_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquaresOf_card_eq_of_periodic
/-- info: 'MPC.MoveTrace.mem_openableSquaresOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_openableSquaresOf
/-- info: 'MPC.MoveTrace.openableSquaresOf_card_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openableSquaresOf_card_eq_of_periodic
-- discovered-check geometry and coverage (periodic traces).
/-- info: 'MPC.neg_mem_king_stepDirs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.neg_mem_king_stepDirs
/-- info: 'MPC.OnRay.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.OnRay.unique
/-- info: 'MPC.ray_of_attack_not_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.ray_of_attack_not_step
/-- info: 'MPC.not_canMoveToOriented_of_blocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.not_canMoveToOriented_of_blocked
/-- info: 'MPC.MoveTrace.openable_glaring_ray_cyclic_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_glaring_ray_cyclic_of_periodic
/-- info: 'MPC.MoveTrace.openable_move_rays_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_move_rays_of_periodic
/-- info: 'MPC.MoveTrace.openable_covered_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_covered_of_periodic
-- the forward potential; knights, lances, and pawns.
/-- info: 'MPC.forwardRank_lt_of_canMoveToOriented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.forwardRank_lt_of_canMoveToOriented
/-- info: 'MPC.MoveTrace.nonGlaringSquaresOf_succ_of_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquaresOf_succ_of_move
/-- info: 'MPC.MoveTrace.nonGlaringSquaresOf_succ_of_not_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.nonGlaringSquaresOf_succ_of_not_move
/-- info: 'MPC.MoveTrace.potential_succ_add_of_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.potential_succ_add_of_move
/-- info: 'MPC.MoveTrace.potential_succ_of_not_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.potential_succ_of_not_move
/-- info: 'MPC.MoveTrace.count_eq_initial_of_step_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.count_eq_initial_of_step_ge
/-- info: 'MPC.MoveTrace.potential_move_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.potential_move_eq_of_periodic
/-- info: 'MPC.MoveTrace.not_nonGlaring_forward_move_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_nonGlaring_forward_move_of_periodic
/-- info: 'MPC.MoveTrace.not_openableMove_forward_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_openableMove_forward_of_periodic
-- gold-type pieces.
/-- info: 'MPC.PieceType.goldType_dirs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.PieceType.goldType_dirs
/-- info: 'MPC.gold_step_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.gold_step_forward
/-- info: 'MPC.OnRay.on_line' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.OnRay.on_line
/-- info: 'MPC.OnRay.cross_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.OnRay.cross_ne_zero
/-- info: 'MPC.forwardRank_lt_of_gold_step_between_rays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.forwardRank_lt_of_gold_step_between_rays
/-- info: 'MPC.MoveTrace.forwardRank_lt_of_nonGlaring_goldType_move_of_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.forwardRank_lt_of_nonGlaring_goldType_move_of_periodic
/-- info: 'MPC.MoveTrace.not_nonGlaring_goldType_move_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_nonGlaring_goldType_move_of_periodic
/-- info: 'MPC.MoveTrace.not_openableMove_goldType_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_openableMove_goldType_of_periodic
-- where a non-glaring silver moves (first half of Lemma 5.1).
/-- info: 'MPC.relTo_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.relTo_inj
/-- info: 'MPC.silver_step_between_lines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.silver_step_between_lines
/-- info: 'MPC.silverSquares_of_step_between_rays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.silverSquares_of_step_between_rays
/-- info: 'MPC.MoveTrace.silverSquares_of_nonGlaring_move_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.silverSquares_of_nonGlaring_move_of_periodic
/-- info: 'MPC.MoveTrace.arrival_of_nonGlaring_move_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.arrival_of_nonGlaring_move_of_periodic
/-- info: 'MPC.MoveTrace.departure_of_nonGlaring_move_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.departure_of_nonGlaring_move_of_periodic
/-- info: 'MPC.MoveTrace.silver_move_reverse_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.silver_move_reverse_of_periodic
-- Lemma 5.1, silvers.
/-- info: 'MPC.forwardSign_opponent' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.forwardSign_opponent
/-- info: 'MPC.forwardSign_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.forwardSign_cases
/-- info: 'MPC.OnRay.relTo_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.OnRay.relTo_eq
/-- info: 'MPC.OnRay.of_relTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.OnRay.of_relTo
/-- info: 'MPC.stepDir_unit_or_forward_knight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.stepDir_unit_or_forward_knight
/-- info: 'MPC.slideDir_of_attack_not_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.slideDir_of_attack_not_step
/-- info: 'MPC.rookDragon_of_slideDir' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.rookDragon_of_slideDir
/-- info: 'MPC.checker_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.checker_cases
/-- info: 'MPC.checkerConstraint_of_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.checkerConstraint_of_checker
/-- info: 'MPC.king_position_of_silver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.king_position_of_silver
/-- info: 'MPC.MoveTrace.mem_rookDragonSquares_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_rookDragonSquares_of
/-- info: 'MPC.MoveTrace.false_of_three_rookDragon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.false_of_three_rookDragon
/-- info: 'MPC.MoveTrace.source_slider_of_nonGlaring_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.source_slider_of_nonGlaring_move
/-- info: 'MPC.MoveTrace.destination_slider_of_nonGlaring_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_slider_of_nonGlaring_move
/-- info: 'MPC.MoveTrace.checker_before_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.checker_before_of_periodic
/-- info: 'MPC.MoveTrace.not_openableMove_silver_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_openableMove_silver_of_periodic
-- Lemma 5.2, rooks and dragons.
/-- info: 'MPC.orth_mem_rookDragon_slideDirs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.orth_mem_rookDragon_slideDirs
/-- info: 'MPC.bishopHorse_of_slideDir' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.bishopHorse_of_slideDir
/-- info: 'MPC.normalize_mul_of_king_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.normalize_mul_of_king_step
/-- info: 'MPC.MoveTrace.mem_bishopHorseSquares_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_bishopHorseSquares_of
/-- info: 'MPC.MoveTrace.bishopHorse_behind_openable_rookDragon_of_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishopHorse_behind_openable_rookDragon_of_periodic
/-- info: 'MPC.MoveTrace.false_of_three_bishopHorse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.false_of_three_bishopHorse
/-- info: 'MPC.MoveTrace.not_openableMove_rookDragon_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_openableMove_rookDragon_of_periodic
-- bishops and horses, the basic facts.
/-- info: 'MPC.diag_of_bishopHorse_slideDir' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.diag_of_bishopHorse_slideDir
/-- info: 'MPC.orth_of_bishopHorse_stepDir' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.orth_of_bishopHorse_stepDir
/-- info: 'MPC.orth_unit_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.orth_unit_cases
/-- info: 'MPC.bishopEdge_of_diag_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.bishopEdge_of_diag_move
/-- info: 'MPC.not_orth_step_between_rays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.not_orth_step_between_rays
/-- info: 'MPC.MoveTrace.openableMove_of_nonGlaring_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openableMove_of_nonGlaring_move
/-- info: 'MPC.MoveTrace.bishopHorse_of_openableMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishopHorse_of_openableMove
/-- info: 'MPC.MoveTrace.bishopHorse_of_nonGlaring_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishopHorse_of_nonGlaring_move
/-- info: 'MPC.MoveTrace.bishopHorse_of_openable_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishopHorse_of_openable_of_periodic
/-- info: 'MPC.MoveTrace.exists_openable_bishopHorse_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.exists_openable_bishopHorse_of_periodic
/-- info: 'MPC.MoveTrace.openable_of_bishopHorse_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.openable_of_bishopHorse_of_periodic
/-- info: 'MPC.MoveTrace.not_glares_bishopHorse_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_glares_bishopHorse_of_periodic
/-- info: 'MPC.MoveTrace.slider_behind_openable_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.slider_behind_openable_of_periodic
/-- info: 'MPC.MoveTrace.orth_ray_of_openable_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.orth_ray_of_openable_of_periodic
/-- info: 'MPC.MoveTrace.bishopEdge_of_nonGlaring_move_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishopEdge_of_nonGlaring_move_of_periodic
-- bishop edges and king candidates.
/-- info: 'MPC.BishopCheckerConstraint.at' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.BishopCheckerConstraint.at
/-- info: 'MPC.bishopCheckerConstraint_of_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.bishopCheckerConstraint_of_checker
/-- info: 'MPC.collinear_kings_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.collinear_kings_iff
/-- info: 'MPC.bishop_destination_facing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.bishop_destination_facing
/-- info: 'MPC.bishop_king_candidates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.bishop_king_candidates
/-- info: 'MPC.facing_edge_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.facing_edge_unique
/-- info: 'MPC.king_off_axes_of_edge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.king_off_axes_of_edge
/-- info: 'MPC.facing_edge_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.facing_edge_signs
/-- info: 'MPC.facing_edge_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.facing_edge_mem_iff
/-- info: 'MPC.MoveTrace.bishop_move_data_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishop_move_data_of_periodic
/-- info: 'MPC.MoveTrace.bishop_moves_facing_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishop_moves_facing_of_periodic
/-- info: 'MPC.MoveTrace.bishop_reverse_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishop_reverse_of_periodic
/-- info: 'MPC.MoveTrace.relTo_king_far_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.relTo_king_far_of_periodic
/-- info: 'MPC.MoveTrace.bishopHorse_square_unique_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishopHorse_square_unique_of_periodic
/-- info: 'MPC.MoveTrace.bishop_configuration_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishop_configuration_of_periodic
-- no bishop edge in front of the enemy king.
/-- info: 'MPC.MoveTrace.source_slider_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.source_slider_far
/-- info: 'MPC.MoveTrace.destination_slider_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_slider_far
/-- info: 'MPC.MoveTrace.bishop_configuration_back_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishop_configuration_back_of_periodic
-- Table 1.
/-- info: 'MPC.bishop_table_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.bishop_table_cases
/-- info: 'MPC.MoveTrace.destination_not_bishopHorse_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_not_bishopHorse_of_periodic
/-- info: 'MPC.MoveTrace.not_bishop_move_past_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_bishop_move_past_of_periodic
/-- info: 'MPC.MoveTrace.bishop_rows_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishop_rows_of_periodic
-- bishops and horses, Proposition 3.8.
/-- info: 'MPC.lineSide_eq_cross' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.lineSide_eq_cross
/-- info: 'MPC.not_step_of_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.not_step_of_multiple
/-- info: 'MPC.OnRay.of_relTo_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.OnRay.of_relTo_sub
/-- info: 'MPC.MoveTrace.false_of_blocked_destination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.false_of_blocked_destination
/-- info: 'MPC.MoveTrace.false_of_blocked_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.false_of_blocked_source
/-- info: 'MPC.MoveTrace.discHCount_before_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.discHCount_before_move
/-- info: 'MPC.MoveTrace.false_of_bishop_case_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.false_of_bishop_case_i
/-- info: 'MPC.MoveTrace.false_of_bishop_case_ii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.false_of_bishop_case_ii
/-- info: 'MPC.MoveTrace.false_of_bishop_rows_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.false_of_bishop_rows_of_periodic
/-- info: 'MPC.MoveTrace.not_openableMove_bishopHorse_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.not_openableMove_bishopHorse_of_periodic
-- the angle key of Definitions 4.2/4.3 (constant on half-lines from the enemy king, lowered by interpositions).
/-- info: 'MPC.vecKey_of_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.vecKey_of_mul
/-- info: 'MPC.vecKey_lt_of_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.vecKey_lt_of_comb
/-- info: 'MPC.angleKey_eq_of_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.angleKey_eq_of_ray
/-- info: 'MPC.angleKey_lt_of_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.angleKey_lt_of_between
-- the checking square of each state, and the angle keys of checkers and destinations.
/-- info: 'MPC.angleKey_eq_of_onRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.angleKey_eq_of_onRay
/-- info: 'MPC.angleKey_lt_of_onRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.angleKey_lt_of_onRay
/-- info: 'MPC.MoveTrace.kingPos_eq_of_mutualPerpetualCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.kingPos_eq_of_mutualPerpetualCheck
/-- info: 'MPC.MoveTrace.exists_checker_of_mutualPerpetualCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.exists_checker_of_mutualPerpetualCheck
/-- info: 'MPC.MoveTrace.isCheckerAt_checkerSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.isCheckerAt_checkerSquare
/-- info: 'MPC.MoveTrace.checkerSquare_eq_of_isCheckerAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.checkerSquare_eq_of_isCheckerAt
/-- info: 'MPC.MoveTrace.checkerSquare_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.checkerSquare_before
/-- info: 'MPC.MoveTrace.destination_eq_or_onRay_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_eq_or_onRay_checker
/-- info: 'MPC.MoveTrace.angleKey_destination_eq_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.angleKey_destination_eq_checker
/-- info: 'MPC.MoveTrace.destination_eq_or_angleKey_lt_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_eq_or_angleKey_lt_checker
/-- info: 'MPC.MoveTrace.lineSide_kings_checkerSquare_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.lineSide_kings_checkerSquare_ne_zero
/-- info: 'MPC.MoveTrace.checkerSquare_succ_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.checkerSquare_succ_cases
-- the angle potential and its change per move (Remarks 4.4/4.5, Lemma 4.7).
/-- info: 'MPC.MoveTrace.mem_ownNonGlaringSquares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_ownNonGlaringSquares
/-- info: 'MPC.MoveTrace.destination_not_mem_nonGlaringSquares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_not_mem_nonGlaringSquares
/-- info: 'MPC.MoveTrace.destination_not_mem_ownNonGlaringSquares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.destination_not_mem_ownNonGlaringSquares
/-- info: 'MPC.MoveTrace.mem_ownNonGlaringSquares_succ_iff_of_untouched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.mem_ownNonGlaringSquares_succ_iff_of_untouched
/-- info: 'MPC.MoveTrace.ownNonGlaringSquares_succ_of_opponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.ownNonGlaringSquares_succ_of_opponent
/-- info: 'MPC.MoveTrace.ownNonGlaringSquares_succ_of_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.ownNonGlaringSquares_succ_of_direct
/-- info: 'MPC.MoveTrace.ownNonGlaringSquares_succ_of_unblocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.ownNonGlaringSquares_succ_of_unblocked
/-- info: 'MPC.MoveTrace.anglePotential_succ_of_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.anglePotential_succ_of_direct
/-- info: 'MPC.MoveTrace.anglePotential_succ_of_turn_opponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.anglePotential_succ_of_turn_opponent
/-- info: 'MPC.MoveTrace.anglePotential_succ_le_of_turn_opponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.anglePotential_succ_le_of_turn_opponent
-- Proposition 4.1 (each side makes a discovered check), from the angle potential and the hands.
/-- info: 'MPC.eq_of_step_le_of_last_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.eq_of_step_le_of_last_eq
/-- info: 'MPC.MoveTrace.anglePotential_last_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.anglePotential_last_eq
/-- info: 'MPC.MoveTrace.hand_card_succ_of_turn_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.hand_card_succ_of_turn_ne
/-- info: 'MPC.MoveTrace.hand_card_succ_of_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.hand_card_succ_of_capture
/-- info: 'MPC.MoveTrace.exists_move_of_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.exists_move_of_turn
/-- info: 'MPC.MoveTrace.discoveredCheckByEachSide_of_mutualPerpetualCheck' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.discoveredCheckByEachSide_of_mutualPerpetualCheck
-- piece families on the board and in hand; DropsFromHand and InitialPieceCountsAtMostTwo.
/-- info: 'MPC.promoteStable_bishopFamily' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.promoteStable_bishopFamily
/-- info: 'MPC.promoteStable_rookFamily' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.promoteStable_rookFamily
/-- info: 'MPC.Board.familyCount_le_familyTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Board.familyCount_le_familyTotal
/-- info: 'MPC.MoveTrace.bishopHorseSquares_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.bishopHorseSquares_card_eq
/-- info: 'MPC.MoveTrace.rookDragonSquares_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.rookDragonSquares_card_eq
-- family totals never rise when drops come from the hand; PieceCountsAtMostTwo derived.
/-- info: 'MPC.sum_add_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.sum_add_two_eq
/-- info: 'MPC.sum_add_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.sum_add_one_eq
/-- info: 'MPC.Board.handFamilyCount_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Board.handFamilyCount_eq
/-- info: 'MPC.applyMove_boardMove_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_boardMove_hand
/-- info: 'MPC.applyMove_dropMove_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_dropMove_hand
/-- info: 'MPC.applyMove_boardMove_handFamilyCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_boardMove_handFamilyCount
/-- info: 'MPC.applyMove_dropMove_handFamilyCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.applyMove_dropMove_handFamilyCount
/-- info: 'MPC.MoveTrace.boardMove_familyTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.boardMove_familyTotal
/-- info: 'MPC.MoveTrace.dropMove_familyTotal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.dropMove_familyTotal_le
/-- info: 'MPC.MoveTrace.familyTotal_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.familyTotal_succ_le
/-- info: 'MPC.MoveTrace.familyTotal_le_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.familyTotal_le_initial
/-- info: 'MPC.MoveTrace.pieceCountsAtMostTwo_of_transitions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.pieceCountsAtMostTwo_of_transitions
/-- info: 'MPC.MoveTrace.pieceCountsAtMostTwo_of_dropsFromHand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.pieceCountsAtMostTwo_of_dropsFromHand
-- drops land on empty squares in periodic traces whose drops come from the hand.
/-- info: 'MPC.promoteStable_any' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.promoteStable_any
/-- info: 'MPC.familyInd_any_eq_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.familyInd_any_eq_zero_iff
/-- info: 'MPC.MoveTrace.dropMove_familyTotal_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.dropMove_familyTotal_add
/-- info: 'MPC.MoveTrace.dropDestinationsEmpty_of_dropsFromHand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.dropDestinationsEmpty_of_dropsFromHand
-- PeriodicMutualCheck (MutualPerpetualCheck without the drop rule) and the main theorem's MutualPerpetualCheck form.
/-- info: 'MPC.MoveTrace.PeriodicMutualCheck.toMutualPerpetualCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.PeriodicMutualCheck.toMutualPerpetualCheck
/-- info: 'MPC.MoveTrace.MutualPerpetualCheck.toPeriodicMutualCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.MutualPerpetualCheck.toPeriodicMutualCheck
/-- info: 'MPC.MoveTrace.periodicMutualCheck_iff_mutualPerpetualCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.MoveTrace.periodicMutualCheck_iff_mutualPerpetualCheck
/-- info: 'MPC.mutual_perpetual_check_impossible_of_mutualPerpetualCheck' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.mutual_perpetual_check_impossible_of_mutualPerpetualCheck

-- the original piece of a promoted piece (demote), and the families closed under demotion.
/-- info: 'MPC.PieceType.demote_demote' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.PieceType.demote_demote
/-- info: 'MPC.PieceType.promote_demote' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.PieceType.promote_demote
/-- info: 'MPC.PromoteStable.demote_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.PromoteStable.demote_iff
/-- info: 'MPC.familyInd_demote' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.familyInd_demote
