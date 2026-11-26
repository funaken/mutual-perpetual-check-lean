#!/usr/bin/env python3
"""Cross-check manuscript names against the explicit Lean audit and source paths."""
import re
from pathlib import Path
from lean_source import without_comments

def declarations(path):
    return list(dict.fromkeys(re.findall(r'\\decl\{([^}]+)\}', Path(path).read_text())))

names = declarations('paper/main.tex')
english = declarations('paper/main_en.tex')
if set(names) != set(english):
    raise SystemExit(f'Manuscripts cite different declarations: {sorted(set(names) ^ set(english))}')
def is_chess(path):
    return path == Path('MPC/Chess.lean') or Path('MPC/Chess') in path.parents

# Shogi names are audited by the publication entry point, chess names by the
# independent chess verification, which pins every public chess theorem.
audits = {False: ('MPC.PaperVerification', without_comments(Path('MPC/PaperVerification.lean').read_text())),
          True: ('MPC.Chess.Verification', without_comments(Path('MPC/Chess/Verification.lean').read_text()))}
rows = ['# 原稿の主要宣言', '',
        '宣言の存在と標準公理のみへの依存は、将棋は`MPC.PaperVerification`、',
        'チェスは`MPC.Chess.Verification`で検査する。',
        '対応行は`python3 scripts/manuscript_refs.py`で再生成する。', '',
        '| 宣言 | 定義・証明 |', '| --- | --- |']
for name in names:
    chess = name.startswith('MPC.Chess.')
    module, audit = audits[chess]
    if not re.search(re.escape(name) + r'(?![\w.])', audit):
        raise SystemExit(f'Not audited in {module}: {name}')
    short = name.rsplit('.',1)[1]
    found = []
    for path in Path('MPC').rglob('*.lean'):
        # Shogi and chess reuse some short names, so search only the cited side.
        if is_chess(path) != chess:
            continue
        source = without_comments(path.read_text())
        match = re.search(r'^(?:noncomputable )?(?:def|theorem) ' + re.escape(short) + r'(?=\s|\()', source, re.M)
        if match:
            line = source[:match.start()].count('\n') + 1
            found.append((path, line))
    if len(found) != 1:
        raise SystemExit(f'Ambiguous source reference: {name}: {found}')
    p, line = found[0]
    rows.append(f'| `{name}` | [{p}:{line}](../../{p}#L{line}) |')
Path('docs/validation/manuscript-declarations.md').write_text('\n'.join(rows)+'\n')
print(f'PASS: {len(names)} manuscript declaration references')
