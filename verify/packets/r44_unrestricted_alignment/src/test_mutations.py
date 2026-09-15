#!/usr/bin/env python3
"""Adversarial controls for selected exact gates; not the proof itself."""
from pathlib import Path
from fractions import Fraction
import copy, json, subprocess, sys, tempfile, time
B=Path(__file__).resolve().parents[1]
solid=json.loads((B/'input/r44_solid.json').read_text())
collision=json.loads((B/'input/companion_collision_certificate.json').read_text())
registered=json.loads((B/'input/candidate_certificate.json').read_text())
tests=[]
with tempfile.TemporaryDirectory(prefix='r44_mutations_') as td:
    tmp=Path(td)
    variants=[]
    x=copy.deepcopy(solid);x['triangles'].pop();variants.append(('missing_triangle','--solid',x))
    x=copy.deepcopy(solid);x['triangles'][0][0],x['triangles'][0][1]=x['triangles'][0][1],x['triangles'][0][0]
    variants.append(('reversed_triangle','--solid',x))
    x=copy.deepcopy(solid)
    apex=tuple(map(Fraction,x['patches'][0]['apex']))
    k=next(i for i,v in enumerate(x['vertices']) if tuple(map(Fraction,v))==apex)
    # An actual geometric change, with stale annotations; mesh extraction must detect it.
    x['vertices'][k][0]=str(Fraction(x['vertices'][k][0])+Fraction(1,100000))
    variants.append(('changed_geometric_apex','--solid',x))
    x=copy.deepcopy(collision);x['witnesses'].pop();variants.append(('missing_rejection_witness','--collisions',x))
    x=copy.deepcopy(collision);x['witnesses'][0]['possible_partners']+=1
    variants.append(('wrong_companion_quantifier','--collisions',x))
    x=copy.deepcopy(registered);x['legal_contacts'].pop();variants.append(('missing_registered_contact','--registered',x))
    for name,flag,data in variants:
        path=tmp/(name+'.json');path.write_text(json.dumps(data))
        start=time.monotonic()
        proc=subprocess.run([sys.executable,str(B/'src/verify_alignment.py'),flag,str(path),'--output',str(tmp/'output.json')],capture_output=True,text=True,timeout=30)
        if proc.returncode==0:raise RuntimeError('Mutation unexpectedly accepted: '+name)
        tests.append({'mutation':name,'rejected':True,'last_error_line':proc.stderr.strip().splitlines()[-1],
                      'seconds':time.monotonic()-start})
r={'status':'PASS','all_mutations_rejected':True,'tests':tests,
   'scope':'Checks selected malformed inputs are rejected. Does not validate the continuous proof.'}
(B/'results/mutation_controls.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
