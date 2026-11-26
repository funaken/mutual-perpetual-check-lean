import MPC.Main
/-!
# MPC.Axioms — 信頼境界と論文対応

独自公理は0件。主定理は`MoveTrace`上で述べ、`PeriodicMutualCheck`、
`DropsFromHand`、`InitialPieceCountsAtMostTwo`を前提とする。
依存するLean標準公理は`propext`、`Classical.choice`、`Quot.sound`のみ。

玉の固定性、開き王手の存在、駒数上限、半平面の不変量は途中で証明する。
実将棋との仕様対応は定義の読解による監査と区別する。
詳細は`docs/publication-model-audit.md`、原論文との対応は同文書の対応表を参照。
過去の公理・モデル移行の記録は`docs/history/axioms-67f7d62.md`に保存した。

本モジュールは主定理のimportと説明だけを持つ。
-/
