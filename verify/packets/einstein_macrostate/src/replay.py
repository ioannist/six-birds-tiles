#!/usr/bin/env python3
"""Replay the two independent finite/geometry checkers for R44."""
from pathlib import Path
import json,subprocess,sys,time,hashlib
B=Path(__file__).resolve().parents[1]
if not __debug__:raise RuntimeError('Run with assertions enabled.')
start=time.monotonic();steps=[]
for name,out in [('verify.py','verification.json'),('edge_audit.py','edge_audit.json')]:
 t=time.monotonic();p=subprocess.run([sys.executable,str(B/'src'/name)],capture_output=True,text=True)
 (B/'results'/(name+'.replay.log')).write_text(p.stdout+p.stderr)
 if p.returncode:
  print(p.stdout);print(p.stderr,file=sys.stderr);raise SystemExit(p.returncode)
 d=json.loads((B/'results'/out).read_text());assert d['status']=='PASS'
 steps.append({'checker':name,'status':d['status'],'seconds':time.monotonic()-t})
r={'status':'PASS','steps':steps,'seconds':time.monotonic()-start,'external_dependencies':[],
   'formal_proof_assistant_verification':False,'external_adversarial_review_completed':False,
   'scope':'Exact finite and mesh gates replayed; unrestricted geometric lemmas supplied in PROOFS.md.'}
(B/'results/replay.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
