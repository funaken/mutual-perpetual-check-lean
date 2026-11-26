# 原稿の主要宣言

宣言の存在と標準公理のみへの依存は、将棋は`MPC.PaperVerification`、
チェスは`MPC.Chess.Verification`で検査する。
対応行は`python3 scripts/manuscript_refs.py`で再生成する。

| 宣言 | 定義・証明 |
| --- | --- |
| `MPC.mem_slidePath_iff_of_exact_steps` | [MPC/Basic/SlidePath.lean:99](../../MPC/Basic/SlidePath.lean#L99) |
| `MPC.mutual_perpetual_check_impossible` | [MPC/Main.lean:59](../../MPC/Main.lean#L59) |
| `MPC.MoveTrace.kingPos_eq_of_periodic` | [MPC/Geometry/KingImmobility.lean:188](../../MPC/Geometry/KingImmobility.lean#L188) |
| `MPC.vecKey_of_mul` | [MPC/Geometry/AngleKey.lean:44](../../MPC/Geometry/AngleKey.lean#L44) |
| `MPC.vecKey_lt_of_comb` | [MPC/Geometry/AngleKey.lean:96](../../MPC/Geometry/AngleKey.lean#L96) |
| `MPC.MoveTrace.anglePotential` | [MPC/Invariants/AnglePotential.lean:57](../../MPC/Invariants/AnglePotential.lean#L57) |
| `MPC.MoveTrace.discoveredCheckByEachSide_of_mutualPerpetualCheck` | [MPC/Invariants/DiscoveredCheckNecessity.lean:128](../../MPC/Invariants/DiscoveredCheckNecessity.lean#L128) |
| `MPC.MoveTrace.discHCount_succ_eq` | [MPC/Invariants/DiscHTrace.lean:157](../../MPC/Invariants/DiscHTrace.lean#L157) |
| `MPC.MoveTrace.discHCount_eq_of_periodic` | [MPC/Invariants/DiscHTrace.lean:324](../../MPC/Invariants/DiscHTrace.lean#L324) |
| `MPC.Chess.mutual_perpetual_check_impossible` | [MPC/Chess/Impossibility.lean:249](../../MPC/Chess/Impossibility.lean#L249) |
| `MPC.Chess.mutual_perpetual_check_impossible_of_fideSamePosition` | [MPC/Chess/FIDERepetition.lean:53](../../MPC/Chess/FIDERepetition.lean#L53) |
| `MPC.Chess.MoveTrace.pieceCount_eq_of_periodic` | [MPC/Chess/PeriodicReduction.lean:39](../../MPC/Chess/PeriodicReduction.lean#L39) |
| `MPC.Chess.MoveTrace.not_castle_of_periodic_checks` | [MPC/Chess/PeriodicReduction.lean:187](../../MPC/Chess/PeriodicReduction.lean#L187) |
| `MPC.Chess.MoveTrace.kingPositions_eq_of_periodic_checks` | [MPC/Chess/KingImmobility.lean:227](../../MPC/Chess/KingImmobility.lean#L227) |
| `MPC.Chess.MoveTrace.checking_piece_is_slider_of_periodic_checks` | [MPC/Chess/CheckerReduction.lean:50](../../MPC/Chess/CheckerReduction.lean#L50) |
| `MPC.Chess.MoveTrace.every_move_between_distinct_checkingRays` | [MPC/Chess/CheckingRayMoves.lean:92](../../MPC/Chess/CheckingRayMoves.lean#L92) |
| `MPC.Chess.MoveTrace.checker_eq_or_beyond_second_of_periodic_checks` | [MPC/Chess/CheckerCrossingOrder.lean:95](../../MPC/Chess/CheckerCrossingOrder.lean#L95) |
| `MPC.Chess.MoveTrace.checker_at_second_departs_of_periodic_checks` | [MPC/Chess/SecondCrossingMoves.lean:159](../../MPC/Chess/SecondCrossingMoves.lean#L159) |
| `MPC.Chess.kingRayRank_add_le_four` | [MPC/Chess/RayAngleRank.lean:129](../../MPC/Chess/RayAngleRank.lean#L129) |
| `MPC.Chess.MoveTrace.checkingRay_rank_le_two_of_periodic_checks` | [MPC/Chess/CheckingRayRank.lean:107](../../MPC/Chess/CheckingRayRank.lean#L107) |
| `MPC.Chess.MoveTrace.figure3_candidates_of_periodic_checks` | [MPC/Chess/Figure3Candidates.lean:65](../../MPC/Chess/Figure3Candidates.lean#L65) |
| `MPC.Chess.MoveTrace.false_of_upper_candidate` | [MPC/Chess/Figure3Moves.lean:175](../../MPC/Chess/Figure3Moves.lean#L175) |
| `MPC.Chess.MoveTrace.false_of_lower_candidate` | [MPC/Chess/Impossibility.lean:107](../../MPC/Chess/Impossibility.lean#L107) |
