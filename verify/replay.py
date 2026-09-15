#!/usr/bin/env python3
"""Single entrypoint for the R44 finite verification.

Runs, unchanged, the two independent checkers shipped with the proof packets
(registered theorem: packets/einstein_macrostate; unrestricted alignment:
packets/r44_unrestricted_alignment), after asserting that the canonical files in
solid/ and certificates/ are byte-identical to the copies those checkers read.
The packets are copied to a temporary directory first so their shipped result
receipts are never overwritten; only verify/replay_report.json is written here.
Standard library only. Do not run with -O.
"""
import hashlib, json, shutil, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
P5 = ROOT / 'verify/packets/einstein_macrostate'
P6 = ROOT / 'verify/packets/r44_unrestricted_alignment'
BOUNDARY_CHECK = ROOT / 'verify/boundary_sphere.py'
TUBE_CHECK = ROOT / 'verify/tube_formula_controls.py'
SUBSTITUTION_CHECK = ROOT / 'verify/substitution_modular_coincidence.py'
SEED_LANGUAGE_CHECK = ROOT / 'verify/seed_language_closure.py'

CANON = {
    'solid/r44_solid.json': ['results/r44_solid.json', 'input/r44_solid.json'],
    'certificates/candidate_certificate.json': ['results/candidate_certificate.json', 'input/candidate_certificate.json'],
    'certificates/companion_collision_certificate.json': ['results/companion_collision_certificate.json', 'input/companion_collision_certificate.json'],
    'certificates/collision_core_witnesses.jsonl.gz': [None, 'results/collision_core_witnesses.jsonl.gz'],
}
EXPECT_SOLID = 'f320d7a0c2d784a3eb29f001dc035808f67591d9ea8d3dd45949e66442f0ed55'

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    assert sys.flags.optimize == 0, 'run without -O (assertions must be enabled)'
    t0 = time.monotonic(); report = {'canonical_sha256': {}, 'steps': []}
    for canon, (in5, in6) in CANON.items():
        h = sha(ROOT / canon); report['canonical_sha256'][canon] = h
        for base, rel in ((P5, in5), (P6, in6)):
            if rel is not None:
                assert sha(base / rel) == h, f'{canon} differs from {base.name}/{rel}'
    assert report['canonical_sha256']['solid/r44_solid.json'] == EXPECT_SOLID
    local_checks = (
        ('boundary_sphere', [
            'python3', str(BOUNDARY_CHECK), str(ROOT / 'solid/r44_solid.json')]),
        ('tube_formula_controls', ['python3', str(TUBE_CHECK)]),
        ('substitution_modular_coincidence', ['python3', str(SUBSTITUTION_CHECK)]),
        ('seed_language_closure', ['python3', str(SEED_LANGUAGE_CHECK)]),
    )
    for name, cmd in local_checks:
        proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        report['steps'].append({'packet': name, 'cmd': ' '.join(cmd),
                                'returncode': proc.returncode,
                                'tail': (proc.stdout + proc.stderr)[-2000:]})
        assert proc.returncode == 0, f'{name}: {cmd} failed\n{proc.stdout}\n{proc.stderr}'
        print(proc.stdout.strip())
    with tempfile.TemporaryDirectory(prefix='r44replay_') as td:
        for src in (P5, P6):
            cwd = Path(td) / src.name
            shutil.copytree(src, cwd, ignore=shutil.ignore_patterns('__pycache__'))
            cmd = ['python3', 'src/replay.py']
            proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
            report['steps'].append({'packet': src.name, 'cmd': ' '.join(cmd), 'returncode': proc.returncode,
                                    'tail': (proc.stdout + proc.stderr)[-2000:]})
            assert proc.returncode == 0, f'{src.name}: {cmd} failed\n{proc.stdout}\n{proc.stderr}'
    report['seconds'] = round(time.monotonic() - t0, 1); report['status'] = 'PASS'
    (ROOT / 'verify/replay_report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'steps'}, indent=2)); print('PASS')

if __name__ == '__main__':
    main()
