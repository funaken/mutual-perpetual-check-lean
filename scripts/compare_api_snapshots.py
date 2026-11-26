#!/usr/bin/env python3
"""Compare two API snapshots from scripts/api_snapshot.lean, e.g. across toolchains.

Usage:
  compare_api_snapshots.py OLD.jsonl NEW.jsonl [--names-out FILE]
                           [--statements OLD.tsv NEW.tsv]

Reports declarations that disappeared or appeared, declarations whose
normalized type changed (see scripts/check_api.py), and declarations whose
axiom set alone changed. For the type changes it lists the smallest differing
`Lean.Expr` subterms, grouped by their head constants. `--names-out` writes the
type-changed names for scripts/api_statements.lean; `--statements` compares the
statements that script printed under each toolchain. See
docs/validation/toolchain-migration-4.36.md.
"""
import argparse
import collections
import json
from pathlib import Path

from check_api import normalized_type

STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def load(path):
    rows = {}
    for line in Path(path).read_text().splitlines():
        name, ty, axioms = json.loads(line)
        rows[name] = (normalized_type(ty), tuple(axioms))
    return rows


def parse(s):
    stack = [[]]
    for t in s.split(' '):
        if t == '(':
            stack.append([])
        elif t == ')':
            x = stack.pop()
            stack[-1].append(x)
        else:
            stack[-1].append(t)
    return stack[0]


def spine(e):
    args = []
    while isinstance(e, list) and e and e[0] == 'Lean.Expr.app':
        args.append(e[2])
        e = e[1]
    return e, args[::-1]


def head(e):
    if not isinstance(e, list):
        return e
    h, _ = spine(e)
    if isinstance(h, list) and len(h) > 1 and h[0] == 'Lean.Expr.const':
        return h[1]
    return h[0] if isinstance(h, list) and h else str(h)


def diff(x, y, out):
    """Collect (old head, new head) for the smallest differing subterms."""
    if x == y:
        return
    if (isinstance(x, list) and isinstance(y, list) and x and y
            and x[0] == y[0] == 'Lean.Expr.app'):
        hx, ax = spine(x)
        hy, ay = spine(y)
        if hx == hy and len(ax) == len(ay):
            for a, b in zip(ax, ay):
                diff(a, b, out)
            return
    elif isinstance(x, list) and isinstance(y, list) and len(x) == len(y) and x[:1] == y[:1]:
        for a, b in zip(x, y):
            diff(a, b, out)
        return
    out.append((head(x), head(y)))


def load_tsv(path):
    return dict(line.split('\t', 1) for line in Path(path).read_text().splitlines() if line)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('old')
    p.add_argument('new')
    p.add_argument('--names-out')
    p.add_argument('--statements', nargs=2, metavar=('OLD_TSV', 'NEW_TSV'))
    a = p.parse_args()
    old, new = load(a.old), load(a.new)
    both = old.keys() & new.keys()
    typed = sorted(n for n in both if old[n][0] != new[n][0])
    axioms_only = sorted(n for n in both if old[n][0] == new[n][0] and old[n][1] != new[n][1])
    print(f'old {len(old)}, new {len(new)}; unchanged {len(both) - len(typed) - len(axioms_only)}, '
          f'type changed {len(typed)}, axioms only {len(axioms_only)}')
    print(f'only in old: {len(old.keys() - new.keys())}')
    for n in sorted(old.keys() - new.keys()):
        print(f'  {n}')
    print(f'only in new: {len(new.keys() - old.keys())}')
    for n in sorted(new.keys() - old.keys()):
        print(f'  {n}')

    changes = collections.Counter()
    for n in both:
        if old[n][1] != new[n][1]:
            removed = sorted(set(old[n][1]) - set(new[n][1]))
            added = sorted(set(new[n][1]) - set(old[n][1]))
            changes[(tuple(removed), tuple(added))] += 1
    print('axiom-set changes (removed -> added): declarations')
    for (removed, added), c in changes.most_common():
        print(f'  {list(removed)} -> {list(added)}: {c}')
    bad = sorted(n for n, (_, ax) in new.items() if set(ax) - STANDARD)
    print(f'non-standard axioms in new: {bad or "none"}')

    kinds, decls = collections.Counter(), collections.Counter()
    for n in typed:
        out = []
        diff(parse(old[n][0]), parse(new[n][0]), out)
        kinds.update(out)
        decls.update(set(out))
    print('smallest Expr differences (old head -> new head): occurrences / declarations')
    for k, c in kinds.most_common():
        print(f'  {k[0]} -> {k[1]}: {c} / {decls[k]}')

    if a.names_out:
        Path(a.names_out).write_text(''.join(n + '\n' for n in typed))
        print(f'wrote {len(typed)} names to {a.names_out}')
    if a.statements:
        s_old, s_new = load_tsv(a.statements[0]), load_tsv(a.statements[1])
        differ = [n for n in typed if s_old.get(n) != s_new.get(n)]
        print(f'printed statements: {len(typed) - len(differ)} identical, {len(differ)} different')
        for n in differ:
            print(f'  {n}\n    old: {s_old.get(n)}\n    new: {s_new.get(n)}')


if __name__ == '__main__':
    main()
