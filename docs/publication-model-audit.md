# 論文用モデル監査

基準コミット: `67f7d62`。監査日: 2026-11-08。
本表は定義と証明の読解に基づく仕様対応の監査であり、実将棋との対応全体をLeanで
証明したものではない。形式化した定理と、その実世界への解釈を区別する。

## 主定理の範囲

`MPC.mutual_perpetual_check_impossible` は、有限手順`tr`と状態ごとの玉位置列`kp`で
`PeriodicMutualCheck kp ∧ DropsFromHand ∧ InitialPieceCountsAtMostTwo`を満たすものが
存在しないと述べる。長さに上限を設けず、初期局面は任意である。

`PeriodicMutualCheck`の9条件は遷移、移動元所有者、各状態の玉配置、自玉安全、
初期の相手玉安全、毎手の相手玉への王手、所有者に応じた移動、周期性、長さ正である。
玉の固定、不動な王手駒、開き王手の存在、半平面count不変性は前提ではない。
連続王手の千日手の反則規定、あるいは求める不可能性そのものを前提に含めない。

## ルールとの対応

参照: [日本将棋連盟の対局規則](https://www.shogi.or.jp/match/taikyoku_rules/)
（2026-11-08閲覧、第4・5・8・10条）。表中の「対応」は定義を読んだ解釈である。

| 項目 | コード上の条件・結果 | 解釈と限界 |
| --- | --- | --- |
| 盤と駒 | `Pos`、`PieceType`、`Board` | 9×9、14駒種、所有者付き駒。駒を追う個体IDは持たない |
| 方向 | `canMoveToOriented` | 先手前方をy正、後手をy負とする。移動差分と所有者で変換した方向表を比較 |
| 遮蔽 | `pathClear`、`mem_slidePath_iff_of_exact_steps` | 厳密整列したslideの両端を除く経路。非整列入力への幾何解釈を仮定しない |
| 駒の存在 | `BoardMoveSourcesOwned` | 手番側の実駒を要求。利き述語単独は攻撃元の存在を要求しない |
| 玉と王手 | `KingsWellPlaced`、`inCheckOriented` | 両所有者の玉の存在・一意性と、相手駒の幾何的利きを別々に指定 |
| 自玉の安全 | `EveryMoveLeavesOwnKingSafe` | 移動後に自玉が攻撃されない。初期局面には`InitialOpponentKingSafe`を要求 |
| 成り | `PieceType.promote`、`applyMove` | 成れる場所の制限と強制成りを緩める。移動方向は成る前の駒種で判定 |
| 捕獲 | `applyMove`、`PieceType.demote` | 取った成駒は元の駒種で持駒に入る。自駒の捕獲をモデル単独では禁止しない |
| 駒打ち | `DropsFromHand` | 手持ちの駒を使う。二歩・打ち歩詰め・行き所の制限は課さない |
| 打ち先 | `dropDestinationsEmpty_of_dropsFromHand` | 追加仮定ではなく、駒数の収支と周期性から空きを導く |
| 周期性 | `IsPeriodic` | 盤上・双方の持駒・手番を含む`BoardState`の始終一致。4回出現は要求しない |
| 駒数 | `InitialPieceCountsAtMostTwo` | 初期状態の盤上と持駒を合算し、角・馬、飛車・竜の各系統を高々2とする |
| 枚数保存への接続 | `pieceCountsAtMostTwo_of_dropsFromHand` | 全状態の大駒上限を初期条件と手の条件から導く |

通常の将棋の局所的な手順規則を満たす周期的な双方連続王手があれば、本モデルの
前提を満たすと解釈する。ここで「局所的」は千日手に対する終局裁定を除く意味である。
その包含の形式的証明、平手初期配置からの到達可能性、4回出現する履歴から周期区間を
切り出すLean定理は本成果に含めない。これらを証明済みと記述しない。

## 論文との対応

| 原論文 | 主なLean宣言 | 形式化上の補足 |
| --- | --- | --- |
| 定理1.1（将棋） | `MPC.mutual_perpetual_check_impossible` | モデルの全前提を型に明示 |
| 命題2.2 | `MPC.MoveTrace.kingPos_eq_of_periodic` | 玉位置は状態別データから出発し、周期性の下で固定性を導く |
| 補題2.6–2.9 | `MPC.MoveTrace.nonGlaringSquares_card_eq_of_periodic`、`afterMove_eq_of_not_glares_of_periodic` | 集合のcardと駒種ごとの不増加を使う |
| 命題3.3・系3.4 | `MPC.MoveTrace.openable_destination_lines_cyclic_of_periodic` | 周期をまたいだ次の移動を扱う |
| 命題3.6 | `MPC.MoveTrace.checker_off_kingLine_of_periodic` | 王手駒が両玉を通る直線外にあることを導く |
| 命題3.8 | `MPC.disc_H_state_total_invariant` | `discHCount_eq_of_periodic`を用いた全状態の不変性 |
| 命題4.1・補題4.7 | `MPC.MoveTrace.discoveredCheckByEachSide_of_mutualPerpetualCheck` | 有理数キーと局面ポテンシャルへ再構成 |
| 第5節・補題5.1/5.2・表1 | `not_openableMove_*_of_periodic`、`false_of_bishop_rows_of_periodic` | 駒種別の除外。半平面不変量を用いるのは角・馬の分岐 |

## 証明の信頼境界

Lean標準公理のみへの依存は、与えた定義と仮定からの導出を保証する。
仕様と将棋の一致、引用の正確さ、原稿中の説明の正しさは別に確認する。
基礎の具体例は、玉の移動、両所有者、成り、捕獲、打ちを検査するが、全モデルの
実将棋対応や独立性を例だけで証明したとは扱わない。

旧モデルの過強な不動性仮定に関する診断は開発経緯である。原論文の誤りとは帰属せず、
現在の証明にも前提として持ち込まない。詳細な履歴は別文書に保存する。
