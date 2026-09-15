#!/usr/bin/env python3
from pathlib import Path
from itertools import product
from fractions import Fraction
import json,hashlib
HERE=Path(__file__).resolve().parent
source=HERE.parent/'r001_chair_control/certificate.json';d=json.loads(source.read_text());P=[(2*x+1,2*y+1) for x,y in d['tile_cells']]
matrices=[]
for swap,sx,sy in product((False,True),(-1,1),(-1,1)):
    matrices.append(((0,sx),(sy,0)) if swap else ((sx,0),(0,sy)))
def mv(A,p):return tuple(sum(a*b for a,b in zip(row,p)) for row in A)
rows=[]
for ci in d['scale2']['covers'][0]:
    target={(2*x+1,2*y+1) for x,y in d['scale2']['candidates'][ci]['cells']};found=None
    for R in matrices:
        RP=[mv(R,p) for p in P]
        for q in sorted(target):
            t2=tuple(a-b for a,b in zip(q,RP[0]))
            if {tuple(a+b for a,b in zip(p,t2)) for p in RP}==target:
                assert all(z%2==0 for z in t2)
                found={'R':R,'translation':[z//2 for z in t2],'target_cells':d['scale2']['candidates'][ci]['cells']};break
        if found:break
    assert found;rows.append(found)
out={'maps':rows,'similarity_ratio':'1/2','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'set_operator':'F(K)=union_i ((R_i K+t_i)/2)','fixed_point':'chair P','scope':'no alternative nonempty compact support for these frozen similarity maps'}
(HERE/'certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(rows)
