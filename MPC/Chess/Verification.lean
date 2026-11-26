import MPC.Chess.Tests.Foundation
import MPC.Chess.Tests.Moves
import MPC.Chess.Tests.PeriodicReduction
import MPC.Chess.Tests.KingImmobility
import MPC.Chess.Tests.Glare
import MPC.Chess.Tests.PeriodicGlare
import MPC.Chess.Tests.OpenableLine
import MPC.Chess.Tests.CheckingRay
import MPC.Chess.Tests.RayIntersection
import MPC.Chess.Tests.KingLineExclusion
import MPC.Chess.Tests.CheckingCrossingOrder
import MPC.Chess.Tests.CheckingCrossingWitness
import MPC.Chess.Tests.KingHalfPlane
import MPC.Chess.Tests.RayAngleRank
import MPC.Chess.Tests.CheckingRayRank
import MPC.Chess.Tests.LatticeFrame
import MPC.Chess.Tests.Figure3Geometry
import MPC.Chess.Tests.Figure3Candidates
import MPC.Chess.Tests.Figure3Moves
import MPC.Chess.Tests.Impossibility
import MPC.Chess.Tests.FIDERepetition

/-! Chess has a separate trust boundary and regression entry point. These checks
certify the impossibility theorem `MPC.Chess.mutual_perpetual_check_impossible`,
its corollary for FIDE repetitions, and the foundation, local moves, periodic reductions, checker classification,
periodic glare preservation, cyclic witnesses, checking-ray moves, rational
crossings, king-line exclusion, finite crossing order, two-crossing witnesses,
both claims of Lemma 6.4, open half-plane classification, the Definition 6.5
angle ranks, lattice frames, the Figure 3 candidates and their elimination
imported here. -/

open Lean in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if (`MPC).isPrefixOf n && !(`MPC.Chess).isPrefixOf n then
      throwError "Chess verification imports shogi declaration {n}"
    if (`MPC.Chess).isPrefixOf n && !n.isInternal then
      for a in ← collectAxioms n do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "{n} uses unexpected axiom {a}"

/-- info: 'MPC.Chess.Color.opponent_opponent' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.Color.opponent_opponent

/-- info: 'MPC.Chess.Color.opponent_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.Color.opponent_ne

/-- info: 'MPC.Chess.not_between_source' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.not_between_source

/-- info: 'MPC.Chess.not_between_destination' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.not_between_destination

/-- info: 'MPC.Chess.pathClear_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.pathClear_empty

/-- info: 'MPC.Chess.pathClear_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.pathClear_mono

/-- info: 'MPC.Chess.attacks_not_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.attacks_not_self

/-- info: 'MPC.Chess.attacks_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.attacks_mono

/-- info: 'MPC.Chess.inCheck_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.inCheck_mono

/-- info: 'MPC.Chess.KingsWellPlaced.king_present' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.KingsWellPlaced.king_present

/-- info: 'MPC.Chess.KingsWellPlaced.positions_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.KingsWellPlaced.positions_injective

/-- info: 'MPC.Chess.KingsWellPlaced.positions_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.KingsWellPlaced.positions_unique

/-- info: 'MPC.Chess.KingsWellPlaced.inCheck_iff_exists_king' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.KingsWellPlaced.inCheck_iff_exists_king

/-- info: 'MPC.Chess.MoveTrace.single_before' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.single_before

/-- info: 'MPC.Chess.MoveTrace.single_after' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.single_after

/-- info: 'MPC.Chess.MoveTrace.single_follows_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.single_follows_iff

/-- info: 'MPC.Chess.CastlingRights.allows_ofFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.CastlingRights.allows_ofFunction

/-- info: 'MPC.Chess.Piece.promote_eq_king_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.Piece.promote_eq_king_iff

/-- info: 'MPC.Chess.Board.relocate_destination' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.Board.relocate_destination

/-- info: 'MPC.Chess.Board.relocate_source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.Board.relocate_source

/-- info: 'MPC.Chess.Board.relocate_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.Board.relocate_other

/-- info: 'MPC.Chess.applyMove_turn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.applyMove_turn

/-- info: 'MPC.Chess.nextEnPassant_eq_some_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.nextEnPassant_eq_some_iff

/-- info: 'MPC.Chess.applyMove_castlingRights_no_gain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.applyMove_castlingRights_no_gain

/-- info: 'MPC.Chess.KingsWellPlaced.ne_of_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.KingsWellPlaced.ne_of_empty

/-- info: 'MPC.Chess.KingsWellPlaced.relocate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.KingsWellPlaced.relocate

/-- info: 'MPC.Chess.KingsWellPlaced.erase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.KingsWellPlaced.erase

/-- info: 'MPC.Chess.DestinationAvailable.not_king' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.DestinationAvailable.not_king

/-- info: 'MPC.Chess.KingsWellPlaced.applyMove' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.KingsWellPlaced.applyMove

/-- info: 'MPC.Chess.LegalMove.kingsWellPlaced_after' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.LegalMove.kingsWellPlaced_after

/-- info: 'MPC.Chess.LegalTransition.turn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.LegalTransition.turn

/-- info: 'MPC.Chess.MoveTrace.turn_after_of_legal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.turn_after_of_legal

/-- info: 'MPC.Chess.Board.weightedSum_relocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Board.weightedSum_relocate

/-- info: 'MPC.Chess.Board.weightedSum_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Board.weightedSum_erase

/-- info: 'MPC.Chess.weightedSum_applyMove_enPassant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.weightedSum_applyMove_enPassant

/-- info: 'MPC.Chess.weightedSum_applyMove_castle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.weightedSum_applyMove_castle

/-- info: 'MPC.Chess.Board.pieceCount_relocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Board.pieceCount_relocate

/-- info: 'MPC.Chess.pieceCount_applyMove_enPassant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.pieceCount_applyMove_enPassant

/-- info: 'MPC.Chess.pieceCount_applyMove_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.pieceCount_applyMove_le

/-- info: 'MPC.Chess.Board.pawnCount_relocate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Board.pawnCount_relocate_le

/-- info: 'MPC.Chess.pawnCount_applyMove_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.pawnCount_applyMove_le

/-- info: 'MPC.Chess.pawnCount_applyMove_promotion_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.pawnCount_applyMove_promotion_lt

/-- info: 'MPC.Chess.Board.pawnProgress_relocate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Board.pawnProgress_relocate_le

/-- info: 'MPC.Chess.Board.pawnProgress_relocate_lt_of_pawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Board.pawnProgress_relocate_lt_of_pawn

/-- info: 'MPC.Chess.pawnProgress_applyMove_castle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.pawnProgress_applyMove_castle

/-- info: 'MPC.Chess.MoveTrace.pieceCount_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.pieceCount_eq_of_periodic

/-- info: 'MPC.Chess.MoveTrace.pawnCount_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.pawnCount_eq_of_periodic

/-- info: 'MPC.Chess.MoveTrace.boardMove_destination_empty_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.boardMove_destination_empty_of_periodic

/-- info: 'MPC.Chess.MoveTrace.not_enPassant_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.not_enPassant_of_periodic

/-- info: 'MPC.Chess.MoveTrace.not_promotion_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.not_promotion_of_periodic

/-- info: 'MPC.Chess.MoveTrace.pawnProgress_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.pawnProgress_eq_of_periodic

/-- info: 'MPC.Chess.MoveTrace.boardMove_piece_ne_pawn_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.boardMove_piece_ne_pawn_of_periodic

/-- info: 'MPC.Chess.MoveTrace.inCheck_turn_of_periodic_checks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.inCheck_turn_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.not_castle_of_periodic_checks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.not_castle_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.ordinary_nonPawn_move_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.ordinary_nonPawn_move_of_periodic_checks

/-- info: 'MPC.Chess.Pos.aligned_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Pos.aligned_comm

/-- info: 'MPC.Chess.king_attack_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.king_attack_symm

/-- info: 'MPC.Chess.attacks_aligned_of_slider' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.attacks_aligned_of_slider

/-- info: 'MPC.Chess.aligned_of_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.aligned_of_between

/-- info: 'MPC.Chess.not_aligned_of_king_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.not_aligned_of_king_step

/-- info: 'MPC.Chess.new_attack_source_between' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.new_attack_source_between

/-- info: 'MPC.Chess.MoveTrace.kingPositions_after_of_legal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.kingPositions_after_of_legal

/-- info: 'MPC.Chess.MoveTrace.ownKing_safe_after_of_legal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.ownKing_safe_after_of_legal

/-- info: 'MPC.Chess.MoveTrace.opponent_safe_of_periodic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.opponent_safe_of_periodic

/-- info: 'MPC.Chess.MoveTrace.kings_not_adjacent_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.kings_not_adjacent_of_periodic

/-- info: 'MPC.Chess.MoveTrace.kingMove_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.kingMove_alignment

/-- info: 'MPC.Chess.MoveTrace.boardMove_piece_ne_king_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.boardMove_piece_ne_king_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.kingPositions_eq_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.kingPositions_eq_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.ordinary_nonKing_nonPawn_move_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.ordinary_nonKing_nonPawn_move_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checking_piece_is_slider_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checking_piece_is_slider_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.not_pawn_check_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.not_pawn_check_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.not_knight_check_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.not_knight_check_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.exists_slider_checker_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.exists_slider_checker_of_periodic_checks

/-- info: 'MPC.Chess.applyBoard_eq_of_not_touches' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.applyBoard_eq_of_not_touches

/-- info: 'MPC.Chess.MoveTrace.immovable_board_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.immovable_board_eq

/-- info: 'MPC.Chess.MoveTrace.glares_of_attacks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.glares_of_attacks

/-- info: 'MPC.Chess.MoveTrace.immovableAt_kingPos_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.immovableAt_kingPos_of_periodic_checks

/-- info: 'MPC.Chess.inCheck_relocate_iff_destination_or_unblocked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.inCheck_relocate_iff_destination_or_unblocked

/-- info: 'MPC.Chess.attacks_of_pathClear' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.attacks_of_pathClear

/-- info: 'MPC.Chess.between_of_between_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.between_of_between_tail

/-- info: 'MPC.Chess.pathClear_source_of_unblockedChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.pathClear_source_of_unblockedChecker

/-- info: 'MPC.Chess.not_unblockedChecker_of_source_attacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.not_unblockedChecker_of_source_attacks

/-- info: 'MPC.Chess.MoveTrace.glares_of_destinationChecker' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.glares_of_destinationChecker

/-- info: 'MPC.Chess.MoveTrace.destination_or_unblocked_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.destination_or_unblocked_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.unblockedChecker_of_destination_not_glares' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.unblockedChecker_of_destination_not_glares

/-- info: 'MPC.Chess.MoveTrace.not_unblockedChecker_of_source_glares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.not_unblockedChecker_of_source_glares

/-- info: 'MPC.Chess.MoveTrace.destinationChecker_of_source_glares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.destinationChecker_of_source_glares

/-- info: 'MPC.Chess.MoveTrace.destination_glares_of_source_glares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.destination_glares_of_source_glares

/-- info: 'MPC.Chess.MoveTrace.mem_nonGlaringSquares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.mem_nonGlaringSquares

/-- info: 'MPC.Chess.MoveTrace.glares_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.glares_congr

/-- info: 'MPC.Chess.MoveTrace.nonGlaringSquares_card_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.nonGlaringSquares_card_succ_le

/-- info: 'MPC.Chess.MoveTrace.nonGlaringSquares_card_succ_lt_of_new_glare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.nonGlaringSquares_card_succ_lt_of_new_glare

/-- info: 'MPC.Chess.MoveTrace.nonGlaringSquares_card_eq_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.nonGlaringSquares_card_eq_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.glares_source_of_destination_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.glares_source_of_destination_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.glares_destination_iff_source_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.glares_destination_iff_source_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.glares_other_iff_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.glares_other_iff_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.unblockedChecker_iff_not_source_glares_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.unblockedChecker_iff_not_source_glares_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.destinationChecker_iff_source_glares_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.destinationChecker_iff_source_glares_of_periodic_checks

/-- info: 'MPC.Chess.attacks_relocate_of_not_between' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.attacks_relocate_of_not_between

/-- info: 'MPC.Chess.MoveTrace.ordinaryMoves_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.ordinaryMoves_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.glaringDestinationsCheck_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.glaringDestinationsCheck_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.line_witness_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.line_witness_persists

/-- info: 'MPC.Chess.MoveTrace.departing_line_witness_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.departing_line_witness_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.destination_between_checker_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.destination_between_checker_of_periodic_checks

/-- info: 'MPC.Chess.cyclicBetween_self_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.cyclicBetween_self_left

/-- info: 'MPC.Chess.cyclicBetween_iff_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.cyclicBetween_iff_of_le

/-- info: 'MPC.Chess.cyclicStepBetween_states' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.cyclicStepBetween_states

/-- info: 'MPC.Chess.MoveTrace.board_eq_of_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.board_eq_of_untouched

/-- info: 'MPC.Chess.MoveTrace.not_touches_of_occupied_before_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.not_touches_of_occupied_before_after

/-- info: 'MPC.Chess.MoveTrace.departure_of_occupied_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.departure_of_occupied_of_periodic

/-- info: 'MPC.Chess.MoveTrace.openable_line_cyclic_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.openable_line_cyclic_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.openable_destination_lines_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.openable_destination_lines_of_periodic_checks

/-- info: 'MPC.Chess.onRay_iff_positive_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRay_iff_positive_steps

/-- info: 'MPC.Chess.OnRay.ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.OnRay.ne

/-- info: 'MPC.Chess.OnRay.aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRay.aligned

/-- info: 'MPC.Chess.OnRay.direction_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRay.direction_unique

/-- info: 'MPC.Chess.exists_onRay_of_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.exists_onRay_of_aligned

/-- info: 'MPC.Chess.OnRay.of_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRay.of_between

/-- info: 'MPC.Chess.OnRay.between_iff_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRay.between_iff_distance

/-- info: 'MPC.Chess.OnRay.eq_of_distance_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRay.eq_of_distance_eq

/-- info: 'MPC.Chess.OnRay.between_of_distance_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRay.between_of_distance_lt

/-- info: 'MPC.Chess.between_of_same_ray_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.between_of_same_ray_exit

/-- info: 'MPC.Chess.pathClear_of_attack_onRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.pathClear_of_attack_onRay

/-- info: 'MPC.Chess.Between.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Between.symm

/-- info: 'MPC.Chess.slider_attack_onRay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.slider_attack_onRay

/-- info: 'MPC.Chess.pathClear_source_of_move_onRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.pathClear_source_of_move_onRay

/-- info: 'MPC.Chess.MoveTrace.exists_checkingRay_of_slider' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.exists_checkingRay_of_slider

/-- info: 'MPC.Chess.MoveTrace.source_is_destination_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.source_is_destination_of_periodic

/-- info: 'MPC.Chess.MoveTrace.destination_on_checkingRay_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.destination_on_checkingRay_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.source_on_checkingRay_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.source_on_checkingRay_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.not_same_ray_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.not_same_ray_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.boardMove_between_distinct_checkingRays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.boardMove_between_distinct_checkingRays

/-- info: 'MPC.Chess.MoveTrace.every_move_between_distinct_checkingRays' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.every_move_between_distinct_checkingRays

/-- info: 'MPC.Chess.RayDirection.opposite_opposite' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.RayDirection.opposite_opposite

/-- info: 'MPC.Chess.RayDirection.opposite_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.RayDirection.opposite_ne

/-- info: 'MPC.Chess.Pos.toPlane_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Pos.toPlane_injective

/-- info: 'MPC.Chess.rayParameter_rayPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayParameter_rayPoint

/-- info: 'MPC.Chess.rayPoint_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayPoint_injective

/-- info: 'MPC.Chess.rayPoint_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayPoint_zero

/-- info: 'MPC.Chess.onRationalRay_iff_nonneg_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRationalRay_iff_nonneg_parameter

/-- info: 'MPC.Chess.onRationalRay_rayPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRationalRay_rayPoint

/-- info: 'MPC.Chess.onRationalRay_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRationalRay_origin

/-- info: 'MPC.Chess.positive_ray_toPlane_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.positive_ray_toPlane_iff

/-- info: 'MPC.Chess.onRationalRay_toPlane_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRationalRay_toPlane_iff

/-- info: 'MPC.Chess.rayPoint_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayPoint_add

/-- info: 'MPC.Chess.rayPoint_opposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayPoint_opposite

/-- info: 'MPC.Chess.onRationalRay_shift_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRationalRay_shift_same

/-- info: 'MPC.Chess.onRationalRay_shift_opposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRationalRay_shift_opposite

/-- info: 'MPC.Chess.rayDet_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayDet_eq_zero_iff

/-- info: 'MPC.Chess.rayOffset_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayOffset_eq_zero_iff

/-- info: 'MPC.Chess.rayIntersectionParameters_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayIntersectionParameters_of_eq

/-- info: 'MPC.Chess.rayIntersectionParameters_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayIntersectionParameters_solve

/-- info: 'MPC.Chess.nonparallelIntersection_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.nonparallelIntersection_eq_some_iff

/-- info: 'MPC.Chess.rationalRay_intersection_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rationalRay_intersection_unique

/-- info: 'MPC.Chess.nonparallelIntersection_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.nonparallelIntersection_eq_none_iff

/-- info: 'MPC.Chess.nonparallelIntersection_eq_none_of_parallel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.nonparallelIntersection_eq_none_of_parallel

/-- info: 'MPC.Chess.parallel_rays_intersect_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.parallel_rays_intersect_iff

/-- info: 'MPC.Chess.MoveTrace.checkingCrossing_iff_white_black' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossing_iff_white_black

/-- info: 'MPC.Chess.MoveTrace.checkingCrossing_toPlane_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossing_toPlane_iff

/-- info: 'MPC.Chess.MoveTrace.checkingCrossing_of_nonparallelIntersection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossing_of_nonparallelIntersection

/-- info: 'MPC.Chess.MoveTrace.boardMove_checkingCrossings_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.boardMove_checkingCrossings_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.every_move_between_checkingCrossings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.every_move_between_checkingCrossings

/-- info: 'MPC.Chess.Pos.collinear_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.Pos.collinear_swap

/-- info: 'MPC.Chess.exists_line_parameter_of_collinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.exists_line_parameter_of_collinear

/-- info: 'MPC.Chess.between_iff_line_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.between_iff_line_parameters

/-- info: 'MPC.Chess.collinear_of_line_parameters' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.collinear_of_line_parameters

/-- info: 'MPC.Chess.kingLine_blocker_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.kingLine_blocker_between

/-- info: 'MPC.Chess.MoveTrace.openable_destination_off_kingLine_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.openable_destination_off_kingLine_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checker_off_kingLine_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checker_off_kingLine_of_periodic_checks

/-- info: 'MPC.Chess.OnRay.collinear_iff_rayOffset_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRay.collinear_iff_rayOffset_eq_zero

/-- info: 'MPC.Chess.MoveTrace.checkingRay_offset_ne_zero_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingRay_offset_ne_zero_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingRay_not_contains_otherKing_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingRay_not_contains_otherKing_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingRay_disjoint_parallel_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingRay_disjoint_parallel_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingCrossing_iff_nonparallelIntersection_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossing_iff_nonparallelIntersection_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingCrossing_ne_king_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossing_ne_king_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.mem_checkingCrossings_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.mem_checkingCrossings_iff

/-- info: 'MPC.Chess.MoveTrace.checkingCrossing_of_mem_checkingCrossings' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossing_of_mem_checkingCrossings

/-- info: 'MPC.Chess.MoveTrace.mem_checkingCrossings_iff_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.mem_checkingCrossings_iff_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingCrossings_finite_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossings_finite_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingCrossings_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossings_card_le

/-- info: 'MPC.Chess.MoveTrace.boardMove_mem_checkingCrossings_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.boardMove_mem_checkingCrossings_of_periodic_checks

/-- info: 'MPC.Chess.planeTaxicabDistance_rayPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.planeTaxicabDistance_rayPoint

/-- info: 'MPC.Chess.OnRationalRay.parameter_lt_iff_distance_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRationalRay.parameter_lt_iff_distance_lt

/-- info: 'MPC.Chess.MoveTrace.mem_rayCrossingParameters_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.mem_rayCrossingParameters_iff

/-- info: 'MPC.Chess.MoveTrace.mem_rayCrossingParameters_iff_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.mem_rayCrossingParameters_iff_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingCrossingAt_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossingAt_parameter

/-- info: 'MPC.Chess.MoveTrace.checkingCrossingAt_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossingAt_mem

/-- info: 'MPC.Chess.MoveTrace.exists_checkingCrossingAt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.exists_checkingCrossingAt_iff

/-- info: 'MPC.Chess.MoveTrace.checkingCrossingAt_parameter_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossingAt_parameter_strictMono

/-- info: 'MPC.Chess.MoveTrace.checkingCrossingAt_distance_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossingAt_distance_strictMono

/-- info: 'MPC.Chess.MoveTrace.firstCheckingCrossing_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.firstCheckingCrossing_spec

/-- info: 'MPC.Chess.MoveTrace.secondCheckingCrossing_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.secondCheckingCrossing_spec

/-- info: 'MPC.Chess.MoveTrace.arrival_piece_departs_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.arrival_piece_departs_of_periodic

/-- info: 'MPC.Chess.MoveTrace.board_eq_of_not_mem_checkingCrossings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.board_eq_of_not_mem_checkingCrossings

/-- info: 'MPC.Chess.MoveTrace.mem_checkingCrossings_of_board_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.mem_checkingCrossings_of_board_ne

/-- info: 'MPC.Chess.MoveTrace.checker_two_crossings_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checker_two_crossings_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingRay_two_crossings_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingRay_two_crossings_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.rayCrossingParameters_card_two_le_of_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.rayCrossingParameters_card_two_le_of_distinct

/-- info: 'MPC.Chess.MoveTrace.secondCheckingCrossing_parameter_le_of_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.secondCheckingCrossing_parameter_le_of_two

/-- info: 'MPC.Chess.MoveTrace.rayCrossingParameters_card_two_le_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.rayCrossingParameters_card_two_le_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checker_parameter_ge_second_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checker_parameter_ge_second_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checker_eq_or_beyond_second_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checker_eq_or_beyond_second_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.crossing_before_second_eq_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.crossing_before_second_eq_first

/-- info: 'MPC.Chess.MoveTrace.occupied_piece_departs_of_not_immovable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.occupied_piece_departs_of_not_immovable

/-- info: 'MPC.Chess.MoveTrace.checker_not_immovable_at_second_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checker_not_immovable_at_second_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checker_at_second_departs_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checker_at_second_departs_of_periodic_checks

/-- info: 'MPC.Chess.halfPlaneCross_rayPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.halfPlaneCross_rayPoint

/-- info: 'MPC.Chess.inKingHalfPlane_swap_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.inKingHalfPlane_swap_iff

/-- info: 'MPC.Chess.exists_unique_kingHalfPlane_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.exists_unique_kingHalfPlane_iff

/-- info: 'MPC.Chess.inKingHalfPlane_rayPoint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.inKingHalfPlane_rayPoint_iff

/-- info: 'MPC.Chess.OnRationalRay.inKingHalfPlane_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.OnRationalRay.inKingHalfPlane_iff

/-- info: 'MPC.Chess.halfPlaneDirections_card_three_or_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.halfPlaneDirections_card_three_or_four

/-- info: 'MPC.Chess.MoveTrace.checkingRay_halfPlane_unique_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingRay_halfPlane_unique_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingCrossing_halfPlane_unique_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossing_halfPlane_unique_of_periodic_checks

/-- info: 'MPC.Chess.kingRayRank_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.kingRayRank_pos

/-- info: 'MPC.Chess.kingRayRank_le_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.kingRayRank_le_four

/-- info: 'MPC.Chess.mem_halfPlaneDirections_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.mem_halfPlaneDirections_iff

/-- info: 'MPC.Chess.HalfPlaneSide.opposite_opposite' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.HalfPlaneSide.opposite_opposite

/-- info: 'MPC.Chess.rayOffset_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayOffset_swap

/-- info: 'MPC.Chess.mem_halfPlaneDirections_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.mem_halfPlaneDirections_swap

/-- info: 'MPC.Chess.halfPlaneDirections_side_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.halfPlaneDirections_side_unique

/-- info: 'MPC.Chess.mem_halfPlaneDirections_iff_side_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.mem_halfPlaneDirections_iff_side_eq

/-- info: 'MPC.Chess.exists_mem_halfPlaneDirections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.exists_mem_halfPlaneDirections

/-- info: 'MPC.Chess.kingRayRank_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.kingRayRank_of_mem

/-- info: 'MPC.Chess.kingRayRank_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.kingRayRank_injOn

/-- info: 'MPC.Chess.kingRayRank_add_le_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.kingRayRank_add_le_four

/-- info: 'MPC.Chess.MoveTrace.checkingCrossing_sides_iff_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingCrossing_sides_iff_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.crossing_checkingRay_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.crossing_checkingRay_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingRay_rank_le_two_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingRay_rank_le_two_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.checkingRay_meets_rank_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.checkingRay_meets_rank_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.halfPlane_checkingRays_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.halfPlane_checkingRays_of_periodic_checks

/-- info: 'MPC.Chess.LatticeFrame.flip_false' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.flip_false

/-- info: 'MPC.Chess.LatticeFrame.flip_true' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.flip_true

/-- info: 'MPC.Chess.LatticeFrame.apply_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.apply_add

/-- info: 'MPC.Chess.LatticeFrame.apply_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.apply_injective

/-- info: 'MPC.Chess.LatticeFrame.neg_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.neg_apply

/-- info: 'MPC.Chess.LatticeFrame.neg_dir' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.neg_dir

/-- info: 'MPC.Chess.LatticeFrame.dir_opposite' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.dir_opposite

/-- info: 'MPC.Chess.LatticeFrame.det_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.det_cases

/-- info: 'MPC.Chess.LatticeFrame.abs_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.abs_det

/-- info: 'MPC.Chess.LatticeFrame.dir_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.dir_vector

/-- info: 'MPC.Chess.LatticeFrame.apply_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.apply_smul

/-- info: 'MPC.Chess.LatticeFrame.apply_fst_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.apply_fst_cases

/-- info: 'MPC.Chess.LatticeFrame.abs_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.abs_apply

/-- info: 'MPC.Chess.rayPoint_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayPoint_dir

/-- info: 'MPC.Chess.onRationalRay_dir_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRationalRay_dir_iff

/-- info: 'MPC.Chess.onRay_dir_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.onRay_dir_iff

/-- info: 'MPC.Chess.rayDot_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayDot_swap

/-- info: 'MPC.Chess.rayOffset_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayOffset_dir

/-- info: 'MPC.Chess.rayDot_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.rayDot_dir

/-- info: 'MPC.Chess.kingRayRank_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.kingRayRank_dir

/-- info: 'MPC.Chess.kingRayRank_dir_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.kingRayRank_dir_swap

/-- info: 'MPC.Chess.mem_halfPlaneDirections_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.mem_halfPlaneDirections_dir

/-- info: 'MPC.Chess.mem_halfPlaneDirections_swap_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.mem_halfPlaneDirections_swap_iff

/-- info: 'MPC.Chess.mem_halfPlaneDirections_opposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.mem_halfPlaneDirections_opposite

/-- info: 'MPC.Chess.apply_eq_toInt_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.apply_eq_toInt_sub

/-- info: 'MPC.Chess.abs_le_seven_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.abs_le_seven_of_frame

/-- info: 'MPC.Chess.frame_crossing_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.frame_crossing_eq

/-- info: 'MPC.Chess.exists_frame_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.exists_frame_canonical

/-- info: 'MPC.Chess.side_sign_mul_det_of_north' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.side_sign_mul_det_of_north

/-- info: 'MPC.Chess.halfPlane_figure3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.halfPlane_figure3

/-- info: 'MPC.Chess.MoveTrace.exists_checkingRay_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.exists_checkingRay_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.halfPlane_candidate_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.halfPlane_candidate_of_periodic_checks

/-- info: 'MPC.Chess.MoveTrace.figure3_candidates_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.figure3_candidates_of_periodic_checks

/-- info: 'MPC.Chess.stepShape_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.stepShape_frame

/-- info: 'MPC.Chess.LatticeFrame.apply_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.LatticeFrame.apply_sub

/-- info: 'MPC.Chess.stepShape_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.stepShape_canonical

/-- info: 'MPC.Chess.MoveTrace.move_stepShape_of_periodic_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.move_stepShape_of_periodic_checks

/-- info: 'MPC.Chess.crossing_northEast_west' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.crossing_northEast_west

/-- info: 'MPC.Chess.crossing_northEast_northWest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.crossing_northEast_northWest

/-- info: 'MPC.Chess.crossing_north_west' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.crossing_north_west

/-- info: 'MPC.Chess.crossing_north_northWest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.crossing_north_northWest

/-- info: 'MPC.Chess.MoveTrace.false_of_two_square_moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.false_of_two_square_moves

/-- info: 'MPC.Chess.MoveTrace.false_of_upper_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.false_of_upper_candidate

/-- info: 'MPC.Chess.MoveTrace.figure3_lower_candidate_of_periodic_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.figure3_lower_candidate_of_periodic_checks

/-- info: 'MPC.Chess.mutual_perpetual_check_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.mutual_perpetual_check_impossible

/-- info: 'MPC.Chess.MoveTrace.false_of_lower_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.false_of_lower_candidate

/-- info: 'MPC.Chess.frame_rational_crossing_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.frame_rational_crossing_eq

/-- info: 'MPC.Chess.crossing_east_southWest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.crossing_east_southWest

/-- info: 'MPC.Chess.not_crossing_northEast_southWest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.not_crossing_northEast_southWest

/-- info: 'MPC.Chess.not_crossing_north_southWest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.not_crossing_north_southWest

/-- info: 'MPC.Chess.not_crossing_north_south' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.not_crossing_north_south

/-- info: 'MPC.Chess.not_crossing_east_west' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.not_crossing_east_west

/-- info: 'MPC.Chess.not_crossing_east_northWest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.not_crossing_east_northWest

/-- info: 'MPC.Chess.lowerRay_crossing_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.lowerRay_crossing_parameter

/-- The exact chess main statement: only positive length, legal moves, king
placement, a check with every move and the recurrence of board and side to move
are assumed. -/
example : ¬ ∃ (tr : MPC.Chess.MoveTrace)
    (kp : Fin (tr.len + 1) → MPC.Chess.Color → MPC.Chess.Pos),
      0 < tr.len ∧ tr.FollowsLegalMoves ∧ tr.KingsWellPlaced kp ∧
        tr.EveryMoveChecksOpponent kp ∧ tr.BoardTurnPeriodic :=
  MPC.Chess.mutual_perpetual_check_impossible

/-- info: 'MPC.Chess.FIDESamePosition.of_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.FIDESamePosition.of_eq

/-- info: 'MPC.Chess.FIDESamePosition.iff_legal_enPassant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.FIDESamePosition.iff_legal_enPassant

/-- info: 'MPC.Chess.MoveTrace.boardTurnPeriodic_of_fideSamePosition' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Chess.MoveTrace.boardTurnPeriodic_of_fideSamePosition

/-- info: 'MPC.Chess.mutual_perpetual_check_impossible_of_fideSamePosition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPC.Chess.mutual_perpetual_check_impossible_of_fideSamePosition

/-- The corollary for FIDE Article 9.2.3 repetitions of the initial position. -/
example : ¬ ∃ (tr : MPC.Chess.MoveTrace)
    (kp : Fin (tr.len + 1) → MPC.Chess.Color → MPC.Chess.Pos),
      0 < tr.len ∧ tr.FollowsLegalMoves ∧ tr.KingsWellPlaced kp ∧
        tr.EveryMoveChecksOpponent kp ∧
          MPC.Chess.FIDESamePosition (tr.states (Fin.last tr.len)) (tr.states 0) :=
  MPC.Chess.mutual_perpetual_check_impossible_of_fideSamePosition
