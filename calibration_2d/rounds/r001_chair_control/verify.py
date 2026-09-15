#!/usr/bin/env python3
"""Independent geometric witnesses; no generator or search functions imported."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent
p=HERE/'certificate.json';d=json.loads(p.read_text())
P=set(map(tuple,d['tile_cells']));assert P=={(0,0),(1,0),(0,1)}
# Orthogonal affine cell maps are checked by all pairwise squared distances.
def is_chair(S):
    if len(S)!=3:return False
    distances=sorted((a[0]-b[0])**2+(a[1]-b[1])**2 for a in S for b in S if a<b)
    return distances==[1,1,2]
expected={'scale2':{(x,y) for x in range(4) for y in range(4) if x<2 or y<2},'rectangle3x2':{(x,y) for x in range(3) for y in range(2)}}
reports={}
for name,target in expected.items():
    block=d[name];assert set(map(tuple,block['target']))==target
    for cover in block['covers']:
        cells=[]
        for i in cover:
            S=set(map(tuple,block['candidates'][i]['cells']));assert is_chair(S)
            cells.extend(S)
        assert len(cells)==len(set(cells)) and set(cells)==target
    assert block['covers']
    reports[name]={'checked_covers':len(block['covers']),'pieces_per_cover':len(block['covers'][0])}
out={'status':'PASS','scope':'each exhibited exact cell partition and congruence; geometric existence and periodic counterexample, not a claim of no other covers','reports':reports,'periodic_tiling_generators':[[3,0],[0,2]],'certificate_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
(HERE/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',reports)
