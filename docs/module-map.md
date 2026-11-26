# モジュール移行表

基準: `67f7d62`。宣言名は保持し、importパスを変更した。旧パスの互換importは提供しない。

| 旧パス | 新パス |
| --- | --- |
| `MPC/Basic/AngleKey.lean` | `MPC/Geometry/AngleKey.lean` |
| `MPC/Basic/AngleKeyVerification.lean` | `MPC/Tests/AngleKey.lean` |
| `MPC/Basic/AnglePotential.lean` | `MPC/Invariants/AnglePotential.lean` |
| `MPC/Basic/AnglePotentialVerification.lean` | `MPC/Tests/AnglePotential.lean` |
| `MPC/Basic/BishopBasics.lean` | `MPC/Pieces/BishopBasics.lean` |
| `MPC/Basic/BishopBasicsVerification.lean` | `MPC/Tests/BishopBasics.lean` |
| `MPC/Basic/BishopDiscH.lean` | `MPC/Pieces/BishopDiscH.lean` |
| `MPC/Basic/BishopDiscHVerification.lean` | `MPC/Tests/BishopDiscH.lean` |
| `MPC/Basic/BishopEdge.lean` | `MPC/Pieces/BishopEdge.lean` |
| `MPC/Basic/BishopEdgeVerification.lean` | `MPC/Tests/BishopEdge.lean` |
| `MPC/Basic/BishopFrontEdge.lean` | `MPC/Pieces/BishopFrontEdge.lean` |
| `MPC/Basic/BishopFrontEdgeVerification.lean` | `MPC/Tests/BishopFrontEdge.lean` |
| `MPC/Basic/BishopTable.lean` | `MPC/Pieces/BishopTable.lean` |
| `MPC/Basic/BishopTableVerification.lean` | `MPC/Tests/BishopTable.lean` |
| `MPC/Basic/CaptureDemoteVerification.lean` | `MPC/Tests/CaptureDemote.lean` |
| `MPC/Basic/Check.lean` | `MPC/Legacy/Check.lean` |
| `MPC/Basic/CheckOrigin.lean` | `MPC/Trace/CheckOrigin.lean` |
| `MPC/Basic/CheckOriginTrace.lean` | `MPC/Trace/CheckOriginTrace.lean` |
| `MPC/Basic/CheckOriginTraceVerification.lean` | `MPC/Tests/CheckOriginTrace.lean` |
| `MPC/Basic/CheckOriginVerification.lean` | `MPC/Tests/CheckOrigin.lean` |
| `MPC/Basic/CheckerAngle.lean` | `MPC/Invariants/CheckerAngle.lean` |
| `MPC/Basic/CheckerAngleVerification.lean` | `MPC/Tests/CheckerAngle.lean` |
| `MPC/Basic/CheckerLocation.lean` | `MPC/Trace/CheckerLocation.lean` |
| `MPC/Basic/CheckerLocationVerification.lean` | `MPC/Tests/CheckerLocation.lean` |
| `MPC/Basic/DemoteVerification.lean` | `MPC/Tests/Demote.lean` |
| `MPC/Basic/DiscHInvariant.lean` | `MPC/Invariants/DiscHInvariant.lean` |
| `MPC/Basic/DiscHTrace.lean` | `MPC/Invariants/DiscHTrace.lean` |
| `MPC/Basic/DiscHTraceVerification.lean` | `MPC/Tests/DiscHTrace.lean` |
| `MPC/Basic/DiscoveredCheckNecessity.lean` | `MPC/Invariants/DiscoveredCheckNecessity.lean` |
| `MPC/Basic/DiscoveredCheckNecessityVerification.lean` | `MPC/Tests/DiscoveredCheckNecessity.lean` |
| `MPC/Basic/DropCheck.lean` | `MPC/Trace/DropCheck.lean` |
| `MPC/Basic/DropCheckVerification.lean` | `MPC/Tests/DropCheck.lean` |
| `MPC/Basic/DropDestinations.lean` | `MPC/Invariants/DropDestinations.lean` |
| `MPC/Basic/DropDestinationsVerification.lean` | `MPC/Tests/DropDestinations.lean` |
| `MPC/Basic/ForwardPotential.lean` | `MPC/Invariants/ForwardPotential.lean` |
| `MPC/Basic/ForwardPotentialVerification.lean` | `MPC/Tests/ForwardPotential.lean` |
| `MPC/Basic/GlaringMove.lean` | `MPC/Glare/GlaringMove.lean` |
| `MPC/Basic/GlaringMoveVerification.lean` | `MPC/Tests/GlaringMove.lean` |
| `MPC/Basic/GoldTypeMove.lean` | `MPC/Pieces/GoldTypeMove.lean` |
| `MPC/Basic/GoldTypeMoveVerification.lean` | `MPC/Tests/GoldTypeMove.lean` |
| `MPC/Basic/HalfPlaneChecker.lean` | `MPC/Geometry/HalfPlaneChecker.lean` |
| `MPC/Basic/HalfPlaneCheckerVerification.lean` | `MPC/Tests/HalfPlaneChecker.lean` |
| `MPC/Basic/KingImmobility.lean` | `MPC/Geometry/KingImmobility.lean` |
| `MPC/Basic/KingImmobilityVerification.lean` | `MPC/Tests/KingImmobility.lean` |
| `MPC/Basic/KingLineChecker.lean` | `MPC/Geometry/KingLineChecker.lean` |
| `MPC/Basic/KingLineCheckerVerification.lean` | `MPC/Tests/KingLineChecker.lean` |
| `MPC/Basic/KingLineOpenable.lean` | `MPC/Geometry/KingLineOpenable.lean` |
| `MPC/Basic/KingLineOpenableVerification.lean` | `MPC/Tests/KingLineOpenable.lean` |
| `MPC/Basic/KingMoveGeometry.lean` | `MPC/Geometry/KingMoveGeometry.lean` |
| `MPC/Basic/KingMoveGeometryVerification.lean` | `MPC/Tests/KingMoveGeometry.lean` |
| `MPC/Basic/KingPlacement.lean` | `MPC/Trace/KingPlacement.lean` |
| `MPC/Basic/KingPlacementPreservation.lean` | `MPC/Trace/KingPlacementPreservation.lean` |
| `MPC/Basic/KingPlacementPreservationVerification.lean` | `MPC/Tests/KingPlacementPreservation.lean` |
| `MPC/Basic/KingPlacementTrace.lean` | `MPC/Trace/KingPlacementTrace.lean` |
| `MPC/Basic/KingPlacementTraceVerification.lean` | `MPC/Tests/KingPlacementTrace.lean` |
| `MPC/Basic/KingPlacementVerification.lean` | `MPC/Tests/KingPlacement.lean` |
| `MPC/Basic/LegacyCheckOrigin.lean` | `MPC/Legacy/CheckOrigin.lean` |
| `MPC/Basic/LegacyCheckOriginVerification.lean` | `MPC/Tests/LegacyCheckOrigin.lean` |
| `MPC/Basic/MainTrace.lean` | `MPC/Trace/MutualCheck.lean` |
| `MPC/Basic/MainTraceVerification.lean` | `MPC/Tests/MainTrace.lean` |
| `MPC/Basic/MoveTrace.lean` | `MPC/Trace/MoveTrace.lean` |
| `MPC/Basic/MoveTraceCheck.lean` | `MPC/Trace/MoveTraceCheck.lean` |
| `MPC/Basic/MoveTraceCheckVerification.lean` | `MPC/Tests/MoveTraceCheck.lean` |
| `MPC/Basic/MoveTraceVerification.lean` | `MPC/Tests/MoveTrace.lean` |
| `MPC/Basic/NonGlaringCount.lean` | `MPC/Glare/NonGlaringCount.lean` |
| `MPC/Basic/NonGlaringCountVerification.lean` | `MPC/Tests/NonGlaringCount.lean` |
| `MPC/Basic/NonGlaringKind.lean` | `MPC/Glare/NonGlaringKind.lean` |
| `MPC/Basic/NonGlaringKindVerification.lean` | `MPC/Tests/NonGlaringKind.lean` |
| `MPC/Basic/OpenableGeometry.lean` | `MPC/Geometry/OpenableGeometry.lean` |
| `MPC/Basic/OpenableGeometryVerification.lean` | `MPC/Tests/OpenableGeometry.lean` |
| `MPC/Basic/OpenableLine.lean` | `MPC/Geometry/OpenableLine.lean` |
| `MPC/Basic/OpenableLineCyclic.lean` | `MPC/Geometry/OpenableLineCyclic.lean` |
| `MPC/Basic/OpenableLineCyclicVerification.lean` | `MPC/Tests/OpenableLineCyclic.lean` |
| `MPC/Basic/OpenableLineVerification.lean` | `MPC/Tests/OpenableLine.lean` |
| `MPC/Basic/OrientedCheckVerification.lean` | `MPC/Tests/OrientedCheck.lean` |
| `MPC/Basic/OrientedMoveVerification.lean` | `MPC/Tests/OrientedMove.lean` |
| `MPC/Basic/PeriodicMutualCheck.lean` | `MPC/Trace/PeriodicMutualCheck.lean` |
| `MPC/Basic/PeriodicMutualCheckVerification.lean` | `MPC/Tests/PeriodicMutualCheck.lean` |
| `MPC/Basic/PieceFamilyCount.lean` | `MPC/Invariants/PieceFamilyCount.lean` |
| `MPC/Basic/PieceFamilyCountVerification.lean` | `MPC/Tests/PieceFamilyCount.lean` |
| `MPC/Basic/PieceFamilyStep.lean` | `MPC/Invariants/PieceFamilyStep.lean` |
| `MPC/Basic/PieceFamilyStepVerification.lean` | `MPC/Tests/PieceFamilyStep.lean` |
| `MPC/Basic/RookDragonLemma.lean` | `MPC/Pieces/RookDragonLemma.lean` |
| `MPC/Basic/RookDragonLemmaVerification.lean` | `MPC/Tests/RookDragonLemma.lean` |
| `MPC/Basic/SilverLemma.lean` | `MPC/Pieces/SilverLemma.lean` |
| `MPC/Basic/SilverLemmaVerification.lean` | `MPC/Tests/SilverLemma.lean` |
| `MPC/Basic/SilverMove.lean` | `MPC/Pieces/SilverMove.lean` |
| `MPC/Basic/SilverMoveVerification.lean` | `MPC/Tests/SilverMove.lean` |
| `MPC/Basic/SlidePathVerification.lean` | `MPC/Tests/SlidePath.lean` |
| `MPC/Basic/SourceUnblocking.lean` | `MPC/Trace/SourceUnblocking.lean` |
| `MPC/Basic/SourceUnblockingVerification.lean` | `MPC/Tests/SourceUnblocking.lean` |
| `MPC/Basic/TraceGlare.lean` | `MPC/Glare/TraceGlare.lean` |
| `MPC/Basic/TraceGlareVerification.lean` | `MPC/Tests/TraceGlare.lean` |
| `MPC/Geometry/Angle.lean` | `MPC/Legacy/Angle.lean` |
| `MPC/MainImportVerification.lean` | `MPC/Tests/MainImport.lean` |
| `MPC/Verification.lean` | `MPC/Audit/Dependencies.lean (guards); MPC/Verification.lean (aggregator)` |

## 切り出した宣言

- `canMoveTo`: `MPC.Legacy.Move`
- 対称駒の旧移動述語との互換定理: `MPC.Legacy.MoveCompatibility`
- 旧王手述語との互換定理: `MPC.Legacy.CheckCompatibility`
- `MoveTrace.BoardMovesFollowCanMoveTo`: `MPC.Legacy.MoveTrace`
- 正しい方向の移動・王手は引き続き`canMoveToOriented`、`attacksOriented`、`inCheckOriented`。名前を入れ替えて意味を変更しない。

## 証明共通化

64個のprivate補題を6個の`MPC.Basic.Lemmas`の補題に共通化した。
銀の幾何の公開宣言は`MPC.Pieces.SilverGeometry`へ分離し、
`SilverLemma`の主証明から玉の相対距離の議論をprivate補題へ抽出した。
公開宣言の型と公理依存は基準スナップショットで比較する。
