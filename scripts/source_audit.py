#!/usr/bin/env python3
"""Fail on proof placeholders/custom axioms and imports that break separation."""
import re
from pathlib import Path
from lean_source import tokens, without_comments

files = [Path('MPC.lean'), *Path('MPC').rglob('*.lean')]
for p in files:
    s = p.read_text()
    # Token scanning avoids counting historical words in comments or messages.
    bad = set(tokens(s)) & {'sorry', 'admit', 'axiom', 'native_decide', 'sorryAx'}
    if bad:
        raise SystemExit(f'{p}: forbidden proof token(s) {sorted(bad)}')

graph = {'.'.join(p.with_suffix('').parts):
         re.findall(r'^import (MPC(?:\.[\w]+)*)', without_comments(p.read_text()), re.M)
         for p in files}

def closure(root):
    seen, todo = set(), [root]
    while todo:
        n = todo.pop()
        if n not in seen:
            seen.add(n)
            todo.extend(graph.get(n, []))
    return seen

for root in ['MPC', 'MPC.Main', 'MPC.PaperVerification']:
    unexpected = [n for n in closure(root) if n.startswith(('MPC.Tests.', 'MPC.Legacy'))
                  or n == 'MPC.Verification']
    if unexpected:
        raise SystemExit(f'{root}: unwanted imports {unexpected}')
print(f'PASS: {len(files)} Lean files; no custom axioms/placeholders/native_decide; production imports isolated')

for root in ['MPC.Chess', 'MPC.Chess.Verification']:
    unexpected = [n for n in closure(root)
                  if n != 'MPC.Chess' and not n.startswith('MPC.Chess.')]
    if unexpected:
        raise SystemExit(f'{root}: chess imports shogi modules {unexpected}')
unexpected = [n for n in closure('MPC.Chess')
              if n.startswith('MPC.Chess.Tests.') or n == 'MPC.Chess.Verification']
if unexpected:
    raise SystemExit(f'MPC.Chess: production imports verification {unexpected}')
print('PASS: chess proof and verification isolated from shogi; chess production excludes tests')
