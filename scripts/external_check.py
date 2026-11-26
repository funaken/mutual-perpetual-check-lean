#!/usr/bin/env python3
"""Check the main theorems with nanoda, a type checker independent of Lean's kernel.

For each main theorem, `leanexport` (shipped with the Lean toolchain) writes the
theorem and every declaration it depends on, including Lean core and Mathlib, in
the lean4export format. `nanoda_bin` (also shipped with the toolchain, written in
Rust) type-checks that whole export from scratch. Only the three standard axioms
are permitted, and any other axiom in the export is a hard error. As negative
controls, nanoda must reject the two declarations of scripts/kernel_canary.py.

nanoda checks that the exported declarations are well typed. The theorem
statements themselves are checked against the paper by scripts/check_api.py and
the #guard_msgs blocks in the verification modules.

Run after the modules are built (verify.sh builds them first).
"""
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
import kernel_canary

ROOT = Path(__file__).resolve().parent.parent
THEOREMS = [
    ('MPC.Main', 'MPC.mutual_perpetual_check_impossible'),
    ('MPC.Chess.Impossibility', 'MPC.Chess.mutual_perpetual_check_impossible'),
    ('MPC.Chess.FIDERepetition', 'MPC.Chess.mutual_perpetual_check_impossible_of_fideSamePosition'),
]
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']


def nanoda(module, theorem, tmp, cwd=ROOT):
    config = Path(tmp) / 'nanoda.json'
    # The Nat and String extensions mirror the GMP and string literal support of Lean's kernel.
    config.write_text(json.dumps(dict(use_stdin=True, permitted_axioms=AXIOMS,
                                      unpermitted_axiom_hard_error=True, nat_extension=True,
                                      string_extension=True, print_success_message=True)))
    export = subprocess.Popen(['lake', 'env', 'leanexport', module, '--', theorem], cwd=cwd,
                              stdout=subprocess.PIPE)
    r = subprocess.run(['lake', 'env', 'nanoda_bin', str(config)], cwd=cwd,
                       stdin=export.stdout, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    export.stdout.close()
    if export.wait():
        raise SystemExit(f'leanexport failed for {theorem}')
    found = re.search(r'Checked (\d+) declarations with no typechecker errors', r.stdout)
    return (int(found.group(1)) if r.returncode == 0 and found else None), r.stdout


def check(module, theorem, tmp):
    count, output = nanoda(module, theorem, tmp)
    if count is None:
        print(output, file=sys.stderr)
        raise SystemExit(f'nanoda rejected {theorem}')
    return count


with tempfile.TemporaryDirectory(prefix='mpc-nanoda-') as tmp:
    counts = [(t, check(m, t, tmp)) for m, t in THEOREMS]
    canary = kernel_canary.build(tmp)
    for m, t in [kernel_canary.HACKED, kernel_canary.AXIOM]:
        if nanoda(m, t, tmp, cwd=canary)[0] is not None:
            raise SystemExit(f'nanoda accepted the canary {t}; the external check is not working')
for theorem, n in counts:
    print(f'nanoda: {theorem}: {n} declarations, standard axioms only')
print(f'PASS: {len(counts)} main theorems pass the external type checker nanoda '
      'with their full dependency closures; it rejects both canaries')
