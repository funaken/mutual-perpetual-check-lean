#!/usr/bin/env python3
"""Check a fresh project directory while reusing the pinned dependency cache.

This intentionally does not claim a from-source rebuild of Lean or Mathlib.
The temporary project has no MPC build products or Git checkout metadata.
"""
import datetime
import json
import os
import platform
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from paper_metrics import ROOT, source_digest


def command(args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


if not (ROOT / '.lake/packages/mathlib/.lake/build/lib').is_dir():
    raise SystemExit('Initialize pinned dependencies and run lake exe cache get first')
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
for p in manifest['packages']:
    actual = command(['git', '-C', str(ROOT / '.lake/packages' / p['name']), 'rev-parse', 'HEAD'])
    if actual != p['rev']:
        raise SystemExit(f"Dependency revision mismatch: {p['name']}")
report = dict(source_sha256=source_digest(),
              started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              platform=platform.platform(), architecture=platform.machine(),
              logical_cpu_count=os.cpu_count(), lean=command(['lake', 'env', 'lean', '--version']),
              python=platform.python_version(),
              command='./scripts/verify.sh',
              conditions='Fresh temporary project without MPC build outputs; pinned third-party caches reused; one elapsed-time measurement; no network fetch during measurement',
              dependencies={p['name']: p['rev'] for p in manifest['packages']})
if platform.system() == 'Darwin':
    report['cpu'] = command(['sysctl', '-n', 'machdep.cpu.brand_string'])
    report['memory_bytes'] = int(command(['sysctl', '-n', 'hw.memsize']))
logpath = ROOT / 'output/logs/clean-build.log'
logpath.parent.mkdir(parents=True, exist_ok=True)
with tempfile.TemporaryDirectory(prefix='mpc-paper-clean-') as d:
    dest = Path(d)
    for name in ['MPC', 'scripts', 'docs/validation', 'paper']:
        shutil.copytree(ROOT / name, dest / name, ignore=shutil.ignore_patterns('__pycache__'))
    for name in ['MPC.lean', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
        shutil.copy2(ROOT / name, dest / name)
    (dest / '.lake').mkdir()
    (dest / '.lake/packages').symlink_to(ROOT / '.lake/packages', target_is_directory=True)
    start = time.monotonic()
    with logpath.open('w') as log:
        result = subprocess.run(['bash', 'scripts/verify.sh'],
                                cwd=dest, stdout=log, stderr=subprocess.STDOUT)
    report['elapsed_seconds'] = round(time.monotonic() - start, 3)
    report['exit_code'] = result.returncode
report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
(ROOT / 'docs/validation/clean-build.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
raise SystemExit(report['exit_code'])
