# 将棋とチェスの双方連続王手を Lean 4 で検証する

正の手数で双方が毎手王手をかけながら元の局面へ戻れるか。このリポジトリは、なんか氏による2024年の不可能性証明を、将棋とチェスの独立したモデルで形式化した研究資料です。

[日本語論文（PDF）](output/pdf/main.pdf) · [English paper (PDF)](output/pdf/main_en.pdf) · [日本語TeX](paper/main.tex) · [English TeX](paper/main_en.tex)

| 対象 | 主定理とモデル |
| --- | --- |
| 将棋 | [`MPC.mutual_perpetual_check_impossible`](MPC/Main.lean)。持駒を含む有限手順を扱い、初期の大駒の枚数条件を明示する。[規則・原論文との対応](docs/publication-model-audit.md) |
| チェス | [`MPC.Chess.mutual_perpetual_check_impossible`](MPC/Chess/Impossibility.lean)。合法手で毎手相手玉を王手すると、盤上配置と手番がともに初期状態へ戻る手順は存在しない。[特殊手・同一局面・原論文との対応](docs/chess-formalization.md) |

## Reproduce the proofs and manuscripts

Install elan, Git and Python 3.9 or later. Run the following commands at the repository root. Lake uses the Lean 4.36.0 toolchain and the dependency revisions in the manifest.

```sh
lake exe cache get
./scripts/verify.sh
```

The verification builds both proofs, checks their stated assumptions and axiom dependencies, runs the regression examples, and checks the declarations cited by both manuscripts. Both main theorems use only `propext`, `Classical.choice` and `Quot.sound`.

`verify.sh` also runs nanoda, an independent type checker, on each main theorem and the FIDE repetition corollary together with their dependencies. To replay the project's declarations through Lean's own kernel, run `python3 scripts/leanchecker_audit.py`. The [audit record](docs/validation/leanchecker.json) and [per-module log](output/logs/leanchecker.log) cover the 179 modules with declarations; the other three contain only imports.

To regenerate the PDFs, install Tectonic or XeLaTeX and Japanese fonts, then run `./scripts/build_paper.sh`. The [reproduction guide](paper/README.md) describes the tools and measurement conditions. See also the [declaration index](docs/validation/manuscript-declarations.md), [source metrics](docs/validation/source-metrics.json), [build record](docs/validation/clean-build.json) and [prior work survey](docs/novelty-review.md).

## Attribution and reuse

The mathematical result is due to Nanka (なんか), third edition, March 9, 2024. [Original publication announcement](https://yaneuraou.yaneu.com/2024/03/03/proof-of-the-impossibility-of-perpetual-check-in-shogi/). For this formalization and its accompanying paper, cite funaken and identify the revision you used. [Citation metadata](CITATION.cff)

The code is licensed under MIT-0. The manuscripts, original figures and PDFs are dedicated under CC0 1.0. See the [license terms and scope](LICENSE).
