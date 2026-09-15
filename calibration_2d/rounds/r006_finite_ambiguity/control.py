#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from math import gcd
import json
rows=[]
for L in (1,2,3,4,5,8,12):
 offsets=set(product(range(L),repeat=2));orbits=[]
 for v in ((1,0),(0,1),(1,1),(2,0),(2,3)):
  todo=set(offsets);lengths=[]
  while todo:
   p=todo.pop();q=((p[0]+v[0])%L,(p[1]+v[1])%L);k=1
   while q!=p:
    assert q in todo;todo.remove(q);q=((q[0]+v[0])%L,(q[1]+v[1])%L);k+=1
   lengths.append(k)
  assert len(set(lengths))==1
  assert lengths[0]==L//gcd(gcd(L,v[0]),v[1])
  assert lengths[0]**2*(v[0]**2+v[1]**2)>=L**2
  orbits.append({'translation':v,'orbit_length':lengths[0],'orbits':len(lengths)})
 rows.append({'L':L,'global_choices':L*L,'inradius':str(Q(L,2)),'radius_per_choice':str(Q(1,2*L)),'actions':orbits})
out={'status':'PASS','periodic_square_controls':rows,'stack_control':[{'horizontal_side':L,'height':1,'inradius':str(Q(1,2)),'vertical_period':[0,0,1]} for L in (1,2,4,8,16)],'scope':'finite actions and dimensional false-target controls; general theorem is proved in RESULT.md'}
(Path(__file__).resolve().parent/'control.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS: complete finite offset actions and the fixed-thickness control')
