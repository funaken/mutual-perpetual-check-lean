# 論文資料の再現

日本語研究原稿は[main.tex](main.tex)、生成済みPDFは[こちら](../output/pdf/main.pdf)。
英語版は[main_en.tex](main_en.tex)、生成済みPDFは[こちら](../output/pdf/main_en.pdf)で、
日本語原稿をAI支援で翻訳したものである。著者名はGitHubアカウント名のfunakenとした。
学会や論文誌へは投稿せず、GitHubでのみ公開する予定である。研究原稿（日英とも）の論旨・引用・
仕様解釈は著者の最終確認を経る必要がある。数学的結果はなんか氏の2024年の原論文に帰属する。

## 固定した証明環境

- Lean **4.36.0**（`lean-toolchain`）。
- Mathlib **fc4f59e577feb1a4956671bc04ac18aaaf8cd842**（タグ`v4.36.0`）。
- 他の依存も`lake-manifest.json`のリビジョンを使う。`lake update`は実行しない。
- `elan`、Python **3.9以降**、Git、初回の依存取得のためのネットワークが必要。

コードの取得後、リポジトリのルートで次を実行する。

```sh
lake exe cache get
./scripts/verify.sh
```

初回はLeanと依存を取得する。Mathlibの配布キャッシュを利用することと、本プロジェクトの
証明項をLeanで再構築することを区別する。Lean/Mathlibそのもののソースからの再構築を
この手順の検証範囲とはしない。

同じ検証は既存の`./scripts/verify_phase6.sh --phase6-complete`でも実行できる。
Gitメタデータのない配布アーカイブでも証明とAPI比較を実行でき、`git diff --check`だけは
Git checkoutで実行する。

検証する内容は次のとおり。

- `lake build`と`lake build MPC.Verification MPC.Axioms MPC.PaperVerification`。
- 独自公理・証明穴・`native_decide`がないこと、および本体のimportがTests/Legacyを読まないこと。
- 主定理の正確な型とLean標準公理だけへの依存。
- Lean 4.36への移行時に記録した**799**個の公開`MPC`宣言の型・公理依存との一致。
  旧基準`67f7d62`（Lean 4.16、768宣言）との対応は[移行記録](../docs/validation/toolchain-migration-4.36.md)にある。
  自動生成の公開宣言を含み、private宣言は含まない。型は束縛変数の名前を除いて比較する。
- 元の回帰検証と依存ガード。共通化した6補題には追加のガードがある。
- 将棋とチェスの主定理、およびFIDE第9.2.3条の系について、Leanのカーネルとは独立した型検査器
  `nanoda_bin`による検査（`scripts/external_check.py`）。

型の指紋比較は補助的な回帰検査であり、Leanの型検査に代わるものではない。
`#print axioms`は、外部の完全な将棋モデルとの対応や原稿の正確さを保証しない。

## クリーンなプロジェクトからの測定

```sh
python3 scripts/measure_clean_build.py
python3 scripts/paper_metrics.py
```

一時ディレクトリへソースをコピーし、**MPCのビルド成果物が一切ない状態**から全検証を実行する。
固定した第三者依存のキャッシュだけを共有する。キャッシュの各Git revisionはmanifestと照合する。
OSを新規インストールした測定、依存ライブラリも含むフルビルド、反復ベンチマークではない。
実行環境・所要時間・ソースのSHA-256は[測定記録](../docs/validation/clean-build.json)、
実際の出力は[ログ](../output/logs/clean-build.log)にある。
測定時に他の重い処理を並走させない。ソースが変わると論文生成は測定のやり直しを要求する。

SHA-256はパス順でソートした`MPC.lean`、`MPC/**/*.lean`、`lakefile.lean`、
`lake-manifest.json`、`lean-toolchain`のパスと内容をNUL区切りで連結した値である。
原稿、測定結果自身、ビルド成果物は含めない。

## 独立した型検査器による検査（nanoda）

`verify.sh`は、3つの主定理それぞれについて、主定理と、それが依存するすべての宣言（Lean本体・Mathlibを含む）を
`leanexport`でlean4export形式に書き出す。Rustで書かれた外部の型検査器`nanoda_bin`が、書き出しの全体を空の環境から
型検査する。どちらもLeanのツールチェーンに含まれる（Lean v4.36.0では、lean4export 3.1.0とnanoda 0.4.17）。
許す公理は`propext`・`Classical.choice`・`Quot.sound`だけで、他の公理が書き出しにあれば失敗する。
Natと文字列のカーネル拡張は、Leanのカーネルに合わせて有効にする。
負の対照として、小さなLeanプロジェクト（`scripts/kernel_canary.py`）を毎回作る。
カーネルの型検査を切って加えた`False`の偽の証明と、標準外の公理から`False`を導く定理を含み、
nanodaがどちらも拒否しなければ失敗する。偽の証明は`lake build`を通ることに注意する。
検査する宣言は、将棋の主定理で約1万個、チェスの主定理とFIDEの系でそれぞれ約8千個あり、合わせて30秒ほどかかる。

nanodaが確かめるのは、書き出した宣言が型として正しいことである。主定理の主張が論文のとおりであることは、
`check_api.py`と検証モジュールの`#guard_msgs`が確かめる。

## カーネルによる再検査（leanchecker）

```sh
python3 scripts/leanchecker_audit.py --record
```

Leanのツールチェーンに含まれる`leanchecker`で、`MPC.lean`と`MPC/**/*.lean`の各モジュールを検査する。
`.olean`に保存された宣言を、そのモジュールのimportだけを読み込んだ環境へ、カーネルで再生する。
カーネルの型検査を経ずに環境へ入った宣言（オプションやメタプログラムによる環境の改ざん）を検出する。
`lake build`と同じカーネルによる再検査であり、独立した型検査器ではない。
MPC以外のimport（Lean本体、Mathlib）の宣言は再生しない。
負の対照として、`scripts/kernel_canary.py`の偽の証明をleancheckerが拒否することを毎回確かめる。

`leanchecker <名前>`は、その名前で始まるすべてのモジュールを1つのプロセスでまとめて検査する。
Lean v4.36.0では、複数のモジュールにまたがるこの実行が、ほぼ毎回セグメンテーション違反（終了コード139）で止まる。
4モジュールでも止まり、スタックを増やしても変わらない（原因は調べていない）。
そのため、スクリプトはモジュールごとに別のプロセスで実行する。
他のモジュール名の接頭辞になる`MPC`・`MPC.Chess`・`MPC.Legacy`は単独では検査できない。
いずれもimportだけのファイルなので対象から外し、宣言が加わった場合はスクリプトが失敗する。

全モジュールで7分ほど（Apple M2 Max、6並列）かかるため、`verify.sh`とCIには含めない。
`--record`は[記録](../docs/validation/leanchecker.json)と[ログ](../output/logs/leanchecker.log)を書く。

## 原稿の生成

Tectonic **0.17.0**、またはXeLaTeXを使う。日本語フォントはNoto Serif/Sans CJK JPを推奨する。
NotoがなければmacOSのヒラギノへフォールバックする。TeX配布物やフォントが違うと
改ページ・PDFバイト列も変わり得るため、PDFのバイト単位の一致は主張しない。

```sh
./scripts/build_paper.sh
```

TectonicがPATH上にない場合は`TECTONIC=/absolute/path/to/tectonic`を指定する。
初回はTeX資材の取得にネットワークが必要。XeLaTeXを使うUbuntuの例：

```sh
sudo apt-get install texlive-xetex texlive-lang-chinese texlive-latex-extra texlive-fonts-recommended fonts-noto-cjk
./scripts/build_paper.sh
```

生成物は`output/pdf/main.pdf`と`output/pdf/main_en.pdf`。ビルドはソース統計を更新し、数式・文字欠落・参照・
はみ出しのエラーを検出する。内容と見た目は別途確認する。今回のPDFは全ページをPNGに
レンダリングして確認した。追試ではPopplerを使い、変更後のPDFを改めて確認する。

```sh
mkdir -p .cache/paper-preview
pdftoppm -scale-to 1250 -png output/pdf/main.pdf .cache/paper-preview/page
```

## 対応表と依存図

- [原論文の命題・モデルとの対応](../docs/publication-model-audit.md)
- [原稿で引用する宣言とソース位置](../docs/validation/manuscript-declarations.md)
- [モジュール移行表](../docs/module-map.md)
- [ソース統計](../docs/validation/source-metrics.json)
- [全import図のGraphvizソース](../docs/validation/imports.dot)

import図の辺`A → B`はAがBをimportする意味であり、証明項が必ずBの全宣言を使う意味ではない。
論文本文の概念図と、`MPC/Audit/Dependencies.lean`の証明項到達検査を区別する。
任意で`dot -Tsvg docs/validation/imports.dot -o output/imports.svg`により拡大可能な図を生成できる。

物理行数はコード行・コメント専用行・空行を分け、コードとコメントが混在する行はコード行に数える。
将棋の本体・検証と依存監査・旧API、チェスの本体・検証を別集計し、Mathlib・設定・文書・スクリプトは含めない。
