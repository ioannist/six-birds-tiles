#!/usr/bin/env python3
"""Replay the new alignment gates and the unchanged upstream finite gates."""
from pathlib import Path
import hashlib, json, subprocess, sys, tempfile, time, zipfile
B=Path(__file__).resolve().parents[1]
start=time.monotonic(); steps=[]
for name in ('verify_alignment.py','replay_core_boxes.py'):
    t=time.monotonic()
    proc=subprocess.run([sys.executable,str(B/'src'/name)],cwd=B,capture_output=True,text=True,timeout=60)
    (B/'results'/f'{name}.replay.log').write_text(proc.stdout+proc.stderr)
    if proc.returncode:raise RuntimeError(f'{name} failed: '+proc.stderr[-2000:])
    steps.append({'checker':name,'status':'PASS','seconds':time.monotonic()-t})
source=B/'upstream/einstein_r44_proof_submission.zip'
with tempfile.TemporaryDirectory(prefix='r44_upstream_replay_') as td:
    with zipfile.ZipFile(source) as z:
        base=Path(td).resolve()
        for name in z.namelist():
            if not (base/name).resolve().is_relative_to(base):
                raise ValueError('Unsafe upstream ZIP member')
        z.extractall(base)
    folder=base/'einstein_macrostate';t=time.monotonic()
    proc=subprocess.run([sys.executable,'src/replay.py'],cwd=folder,capture_output=True,text=True,timeout=60)
    (B/'results/upstream_replay.log').write_text(proc.stdout+proc.stderr)
    if proc.returncode:raise RuntimeError('Upstream replay failed: '+proc.stderr[-2000:])
    details=json.loads(proc.stdout)
    steps.append({'checker':'unchanged upstream replay','status':'PASS','details':details,
                  'seconds':time.monotonic()-t})
r={'status':'PASS','steps':steps,'seconds':time.monotonic()-start,
   'source_archive_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
   'scope':'Exact finite and actual-mesh gates replayed; continuous alignment theorem in ALIGNMENT_PROOF.md.',
   'external_dependencies':[],'external_adversarial_review':False,'proof_assistant_formalization':False}
(B/'results/replay.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
