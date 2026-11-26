#!/usr/bin/env python3
"""Compare exported declaration types modulo binder names and formatting.

The snapshot includes generated public declarations. Internal/private names are
excluded. This is a regression fingerprint, not a replacement for Lean checking.
"""
import hashlib
import json
import re
import sys
from pathlib import Path


def normalized_type(s):
    ts = re.findall(r'"(?:\\.|[^"\\])*"|[()]|[^\s()]+', s)
    out = []
    i = 0
    while i < len(ts):
        t = ts[i]
        out.append(t)
        i += 1
        if t in ('Lean.Expr.forallE', 'Lean.Expr.lam', 'Lean.Expr.letE'):
            if ts[i] == '(':
                depth = 1
                i += 1
                while depth:
                    depth += (ts[i] == '(') - (ts[i] == ')')
                    i += 1
            else:
                i += 1
            out.append('Lean.Name.anonymous')
    return ' '.join(out)


def fingerprints(file):
    result = {}
    for line in Path(file).read_text().splitlines():
        name, ty, axioms = json.loads(line)
        result[name] = {'type_sha256': hashlib.sha256(normalized_type(ty).encode()).hexdigest(),
                        'axioms': axioms}
    return result


if __name__ == '__main__':
    baseline = json.loads(Path('docs/validation/api-baseline.json').read_text())['declarations']
    current = fingerprints(sys.argv[1])
    missing = sorted(baseline.keys() - current.keys())
    changed = sorted(n for n in baseline.keys() & current.keys() if baseline[n] != current[n])
    if missing or changed:
        raise SystemExit(f'Missing declarations: {missing}\nChanged types/dependencies: {changed}')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    unexpected = {n: r['axioms'] for n, r in current.items() if set(r['axioms']) - allowed}
    if unexpected:
        raise SystemExit(f'Unexpected axioms: {unexpected}')
    print(f'PASS: {len(baseline)} baseline declaration types/axioms preserved; '
          f'{len(current) - len(baseline)} new declarations use only standard axioms')
