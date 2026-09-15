#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
HERE=Path(__file__).resolve().parent
p=HERE/'certificate.json';d=json.loads(p.read_text());source=HERE.parent/'r001_chair_control/certificate.json'
assert hashlib.sha256(source.read_bytes()).hexdigest()==d['source_sha256']
receipt=json.loads((source.parent/'verification.json').read_text());assert receipt['status']=='PASS' and receipt['certificate_sha256']==d['source_sha256']
centers=[(Q(1,2),Q(1,2)),(Q(3,2),Q(1,2)),(Q(1,2),Q(3,2))];allcells=[]
for row in d['maps']:
 R=row['R'];t=row['translation']
 assert [[sum(R[k][i]*R[k][j] for k in range(2)) for j in range(2)] for i in range(2)]==[[1,0],[0,1]]
 mapped=[tuple(sum(R[i][j]*p[j] for j in range(2))+t[i] for i in range(2)) for p in centers]
 cells=[tuple(int(z-Q(1,2)) for z in p) for p in mapped]
 assert set(cells)==set(map(tuple,row['target_cells']))
 allcells+=cells
assert len(allcells)==len(set(allcells))==12
assert set(allcells)=={(x,y) for x in range(4) for y in range(4) if x<2 or y<2}
assert Q(d['similarity_ratio'])==Q(1,2)
out={'status':'PASS','scope':'four orthogonal affine maps, exact chair fixed-point cover and contraction factor; uniqueness for all compact alternatives proved in RESULT.md','certificate_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
(HERE/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS')
