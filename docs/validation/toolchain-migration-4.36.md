# Lean v4.36.0 への移行記録

Lean 4.16.0 / Mathlib `v4.16.0`（`a6276f4`）から、Lean 4.36.0（コミット`611c117bfaf7`）/
Mathlib `v4.36.0`（`fc4f59e`）へ移行したときの、公開宣言の比較を記録する。
移行では宣言の主張を変えていない。

[API の基準](api-baseline.json)は、この移行で Lean 4.36 のスナップショットから記録し直した。
旧基準は`67f7d62`（Lean 4.16）の768宣言である。移行直前の master（`3544056`）は、Lean 4.16 で
旧基準と一致していた（`check_api.py`：768宣言が一致、追加6宣言は標準公理のみ）。
以下は、この`3544056`（Lean 4.16、774宣言）と移行後（Lean 4.36、799宣言）の比較である。

## 結果

| 区分 | 件数 | 内容 |
|---|---:|---|
| 変化なし | 608 | 正規化した型と公理依存が一致 |
| 型の指紋が変化 | 84 | 表示した主張はすべて一致（下記） |
| 公理依存だけ変化 | 53 | すべて標準3公理の範囲内 |
| 4.16 にだけある | 29 | 自動生成の宣言（`*.proof_N`、`toCtorIdx`、命題構造体の`noConfusion`、`match_1`） |
| 4.36 にだけある | 54 | 自動生成の宣言（`ctorIdx`、`*.elim`、`ctorElim`、`congr_simp`、`decEq`、`repr`など） |

標準3公理（`propext`・`Classical.choice`・`Quot.sound`）以外に依存する宣言は、どちらにもない。
将棋の主定理`MPC.mutual_perpetual_check_impossible`とチェスの主定理
`MPC.Chess.mutual_perpetual_check_impossible`は、どちらも標準3公理だけに依存する。

### 型の指紋が変わった84件

記法・構造体インスタンス記法・Unicodeの`fun`を外し、名前を完全名で表示すると
（[`api_statements.lean`](../../scripts/api_statements.lean)）、84件とも両方のツールチェーンで
**文字列が完全に一致する**。この表示では、暗黙引数・インスタンス・証明項は省かれる。

`Lean.Expr`の水準で最小の差分を取ると、差は次に限られる。

| 4.16 | 4.36 | 箇所 / 宣言 | 理由 |
|---|---|---:|---|
| `Nat.instNeZeroSucc` | `instNeZeroNatHAdd_1` | 189 / 58 | `Fin (n+1)`の`NeZero`インスタンス。`NeZero`は命題 |
| `Finset.instMembership` | `SetLike.instMembership` | 30 / 19 | Mathlibで`Finset`の`∈`が`SetLike`を経由するようになった |
| `Option.instDecidableEq` | `Option.decidableEqNone` | 2 / 2 | 定義の等式補題（`*.eq_1`）の中の`x = none`の決定手続き |
| `*.proof_N` | `*._proof_N` | 14 / 3 | 型の中に現れる補助証明の名前 |
| 衛生的な名前 | 衛生的な名前 | 14 / 4 | 自動生成の`noConfusion`・`noConfusionType`の宇宙変数名 |

どれも主張の意味を変えない。インスタンスは同じ型クラスの別の項であり、証明項は証明無関係性により区別されない。

### 公理依存だけが変わった53件

| 外れた | 加わった | 宣言 |
|---|---|---:|
| | `propext` | 44 |
| | `Classical.choice`、`Quot.sound` | 5 |
| | `Classical.choice` | 2 |
| `Quot.sound` | | 2 |

これに合わせ、`#guard_msgs`で固定した`#print axioms`の出力を32件更新した
（`MPC/Audit/Dependencies.lean` 21件、`MPC/Chess/Verification.lean` 11件）。主定理のガードは変わっていない。

## 再現の手順

Lean 4.36 のリポジトリのルートで、移行後のスナップショットを取る。

```sh
lake exe cache get
lake build MPC.Verification MPC.Legacy
MPC_API_OUTPUT="$PWD/new.jsonl" lake env lean scripts/api_snapshot.lean
```

配布物に同梱する基準との比較には `python3 scripts/check_api.py new.jsonl` を使う。
