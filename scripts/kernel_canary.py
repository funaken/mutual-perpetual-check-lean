#!/usr/bin/env python3
"""Build a tiny Lean project with declarations that a kernel checker must reject.

`Canary.Hacked` adds `canary_false : False` with the value `Nat.zero` while the
kernel's type check is switched off (`debug.skipKernelTC`), so `lake build`
accepts it. `Canary.Axiom` proves False from an extra axiom. The audits run their
checker on these as negative controls, so a checker that accepts everything fails.
"""
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HACKED = ('Canary.Hacked', 'canary_false')
AXIOM = ('Canary.Axiom', 'canary_from_axiom')
FILES = {
    'lakefile.lean': 'import Lake\nopen Lake DSL\npackage canary\n'
                     'lean_lib Canary where\n  roots := #[`Canary.Hacked, `Canary.Axiom]\n',
    'Canary/Hacked.lean': '''import Lean
open Lean Elab Command

-- A "proof" of False that skips the kernel's type check.
run_cmd liftCoreM do
  withOptions (fun o => o.setBool `debug.skipKernelTC true) do
    addDecl <| .thmDecl { name := `canary_false, levelParams := [],
                          type := mkConst ``False, value := mkConst ``Nat.zero }
''',
    'Canary/Axiom.lean': 'axiom canary_axiom : False\n'
                         'theorem canary_from_axiom : False := canary_axiom\n',
}


def build(tmp):
    """Write and build the canary project in the directory tmp; return its path."""
    project = Path(tmp) / 'canary'
    for name, text in FILES.items():
        (project / name).parent.mkdir(parents=True, exist_ok=True)
        (project / name).write_text(text)
    shutil.copy2(ROOT / 'lean-toolchain', project / 'lean-toolchain')
    r = subprocess.run(['lake', 'build', 'Canary'], cwd=project,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if r.returncode:
        raise SystemExit('Could not build the kernel canary:\n' + r.stdout)
    return project
