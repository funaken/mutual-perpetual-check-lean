#!/usr/bin/env python3
"""Replay the declarations of every MPC module through the Lean kernel again.

`leanchecker` ships with the Lean toolchain. For one module it loads the
environment of the module's imports, then replays the declarations stored in
the module's .olean through the kernel. This detects declarations that entered
the environment without a kernel check ("environment hacking"). It uses the
same kernel as `lake build`, so it is not an independent verifier, and it does
not replay the imports outside MPC (Lean core, Mathlib).

`leanchecker Foo` checks every module whose name starts with `Foo`, all in one
process. In Lean v4.36.0 such runs almost always crash with a segmentation
fault (exit 139) here, so this script gives each module its own process. A module whose name is
a prefix of another module's cannot be checked on its own this way. Such a
module must contain only imports, and it is reported as skipped. As a negative
control, leanchecker must reject the hacked declaration of scripts/kernel_canary.py.

Usage: python3 scripts/leanchecker_audit.py [--jobs N] [--record] [MODULE ...]
Without MODULE, every module is checked. --record writes
docs/validation/leanchecker.json and output/logs/leanchecker.log, and needs a full run.
"""
import argparse
import concurrent.futures
import datetime
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from lean_source import without_comments
import kernel_canary

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / 'docs/validation/leanchecker.json'
LOG = ROOT / 'output/logs/leanchecker.log'


def module_files():
    return sorted([ROOT / 'MPC.lean', *ROOT.glob('MPC/**/*.lean')])


def module_name(path):
    return '.'.join(path.relative_to(ROOT).with_suffix('').parts)


def imports_only(path):
    return all(not line.strip() or re.match(r'import\s', line.strip())
               for line in without_comments(path.read_text()).splitlines())


def source_digest():
    # Same encoding as paper_metrics.source_digest, over every Lean source.
    h = hashlib.sha256()
    for p in sorted([*module_files(), ROOT / 'lakefile.lean', ROOT / 'lake-manifest.json',
                     ROOT / 'lean-toolchain']):
        h.update(str(p.relative_to(ROOT)).encode() + b'\0' + p.read_bytes() + b'\0')
    return h.hexdigest()


def command(args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def check(module, cwd=ROOT):
    start = time.monotonic()
    r = subprocess.run(['lake', 'env', 'leanchecker', module], cwd=cwd,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return module, r.returncode, round(time.monotonic() - start, 1), r.stdout.strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--jobs', type=int, default=min(os.cpu_count() or 1, 6))
    ap.add_argument('--record', action='store_true')
    ap.add_argument('modules', nargs='*', help='check only these modules')
    args = ap.parse_args()
    if args.record and args.modules:
        ap.error('--record needs a run over every module')

    files = {module_name(p): p for p in module_files()}
    names = sorted(files)
    parents = {m for m in names if any(n.startswith(m + '.') for n in names)}
    for m in sorted(parents):
        if not imports_only(files[m]):
            raise SystemExit(f'{m} has declarations and is a prefix of other modules; '
                             'leanchecker cannot check it alone. Move its declarations.')
    targets = [m for m in names if m not in parents]
    if args.modules:
        unknown = sorted(set(args.modules) - set(names))
        if unknown:
            ap.error('unknown module(s): ' + ', '.join(unknown))
        targets = [m for m in targets if m in args.modules]
        parents = {m for m in parents if m in args.modules}

    # leanchecker reads the .olean files, so build every module from these sources first.
    build = subprocess.run(['lake', 'build', *names], cwd=ROOT,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if build.returncode:
        print(build.stdout, file=sys.stderr)
        raise SystemExit('lake build failed; leanchecker needs current .olean files')

    with tempfile.TemporaryDirectory(prefix='mpc-canary-') as tmp:
        _, code, _, output = check(kernel_canary.HACKED[0], cwd=kernel_canary.build(tmp))
    if code == 0 or 'found a problem' not in output:
        raise SystemExit('leanchecker accepted the canary; the audit is not working:\n' + output)

    started = datetime.datetime.now(datetime.timezone.utc)
    start = time.monotonic()
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for module, code, seconds, output in pool.map(check, targets):
            results.append((module, code, seconds, output))
            print(f"{'ok  ' if code == 0 else 'FAIL'} {seconds:6.1f}s {module}", flush=True)
            if output:
                print('     ' + output.replace('\n', '\n     '), flush=True)
    elapsed = round(time.monotonic() - start, 1)
    failures = [m for m, code, _, _ in results if code != 0]

    lines = [f"{'ok  ' if code == 0 else 'FAIL'} exit={code} {seconds:6.1f}s {module}"
             + (f"\n     {output}" if output else '')
             for module, code, seconds, output in results]
    lines += [f'skip (imports only) {m}' for m in sorted(parents)]
    summary = (f'leanchecker replayed {len(targets)} modules ({len(failures)} failed); '
               f'skipped {len(parents)} import-only modules; {elapsed} s with {args.jobs} jobs; '
               'rejected the canary')
    if args.record:
        report = dict(source_sha256=source_digest(), started_utc=started.isoformat(),
                      platform=platform.platform(), architecture=platform.machine(),
                      logical_cpu_count=os.cpu_count(),
                      lean=command(['lake', 'env', 'lean', '--version']),
                      python=platform.python_version(),
                      command=f'python3 scripts/leanchecker_audit.py --jobs {args.jobs} --record',
                      checker='leanchecker (Lean toolchain), one process per module',
                      modules_checked=len(targets), modules_failed=failures,
                      modules_skipped={m: 'imports only' for m in sorted(parents)},
                      elapsed_seconds=elapsed, jobs=args.jobs,
                      exit_code=1 if failures else 0)
        if platform.system() == 'Darwin':
            report['cpu'] = command(['sysctl', '-n', 'machdep.cpu.brand_string'])
            report['memory_bytes'] = int(command(['sysctl', '-n', 'hw.memsize']))
        report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        LOG.parent.mkdir(parents=True, exist_ok=True)
        LOG.write_text('\n'.join(lines + [summary]) + '\n')
        RECORD.write_text(json.dumps(report, indent=2) + '\n')
    if failures:
        print(f'FAIL: {summary}: ' + ', '.join(failures), file=sys.stderr)
        return 1
    print(f'PASS: {summary}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
