#!/usr/bin/env python3
"""Exact actual-mesh audit of every non-flat dihedral used in alignment."""
from fractions import Fraction as F
from collections import defaultdict,Counter
from pathlib import Path
import json,time
B=Path(__file__).resolve().parents[1];start=time.monotonic();S=json.loads((B/'results/r44_solid.json').read_text());V=[tuple(map(F,p)) for p in S['vertices']];T=S['triangles'];lookup={p:i for i,p in enumerate(V)}
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
N=[cross(sub(V[t[1]],V[t[0]]),sub(V[t[2]],V[t[0]])) for t in T];inc=defaultdict(list)
for i,t in enumerate(T):
 for a,b in zip(t,t[1:]+t[:1]):inc[tuple(sorted((a,b)))].append(i)
expected={}
for p in S['patches']:
 base=[lookup[tuple(map(F,q))] for q in p['base']];apex=lookup[tuple(map(F,p['apex']))];j=abs(p['coefficient']);sign=1 if p['coefficient']>0 else -1
 for i in range(4):
  e=tuple(sorted((base[i],base[(i+1)%4])));assert e not in expected;expected[e]=('alpha',j,sign)
  e=tuple(sorted((base[i],apex)));assert e not in expected;expected[e]=('beta',j,-sign)
assert len(expected)==1536
hist=Counter();seen={}
for edge,ids in inc.items():
 assert len(ids)==2;i,k=ids;n,m=N[i],N[k]
 cosine_squared=dot(n,m)**2/(dot(n,n)*dot(m,m))
 other=next(v for v in T[k] if v not in edge)
 side=dot(n,sub(V[other],V[edge[0]]));sgn=(side>0)-(side<0)
 if edge in expected:
  kind,j,sign=expected[edge];ratio=F(j,100);target=1/(1+ratio*ratio)**(1 if kind=='alpha' else 2)
  assert cosine_squared==target and dot(n,m)>0 and sgn==sign
  length2=dot(sub(V[edge[0]],V[edge[1]]),sub(V[edge[0]],V[edge[1]]))
  h=F(j,10000);eta=F(1,100)
  assert length2==(4*eta*eta if kind=='alpha' else 2*eta*eta+h*h)
  hist[kind,j,sgn]+=1
 else:
  assert cosine_squared in (F(0),F(1))
  if cosine_squared==1:assert dot(n,m)>0 and sgn==0;hist['flat',0,0]+=1
  else:assert sgn in(-1,1);hist['coarse',0,sgn]+=1
for j in range(1,13):
 for kind in ['alpha','beta']:
  assert hist[kind,j,1]==32 and hist[kind,j,-1]==32
r={'status':'PASS','all_mesh_edges_checked':len(inc),'feature_edges_checked':len(expected),'all_24_distinct_feature_angle_magnitudes_verified_from_mesh':True,'feature_angles_both_signs_each_count':32,'unlisted_nonflat_angle_types':0,'edge_histogram':[[*k,n] for k,n in sorted(hist.items())],'seconds':time.monotonic()-start}
(B/'results/edge_audit.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
