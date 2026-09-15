"""Exact three-dimensional chair substitution. Only integer arithmetic."""
from itertools import product
from collections import defaultdict
BITS=tuple(product((0,1),repeat=3))
P=frozenset(x for x in BITS if x!=(1,1,1))
I=(1,1,1)
SIGNS=tuple(product((-1,1),repeat=3))
ROOT=(I,(0,0,0))
CHILDREN=tuple((tuple(1-2*b for b in a),tuple(4*b for b in a)) for a in BITS if a!=(1,1,1))+((I,(1,1,1)),)
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def sub(x,y):return tuple(a-b for a,b in zip(x,y))
def scale(a,x):return tuple(a*b for b in x)
def sign(s,x):return tuple(a*b for a,b in zip(s,x))
def cells(pose):
 s,t=pose
 return frozenset(tuple(s[i]*x[i]+t[i]-(s[i]==-1) for i in range(3)) for x in P)
def faces(pose):
 S=cells(pose);out={}
 for x in S:
  for axis in range(3):
   for side in (-1,1):
    n=list(x);n[axis]+=side
    if tuple(n) in S:continue
    c=list(scale(2,x));c=[v+1 for v in c];c[axis]+=side
    out[(axis,tuple(c))]=side
 return out
NATIVE_FACES=tuple(sorted(faces(ROOT).items()))
def refinements(pose):
 s,t=pose
 return tuple((sign(s,r),add(scale(2,t),sign(s,u))) for r,u in CHILDREN)
def normalize(p,q):
 s,t=p;r,u=q
 return sign(s,r),sign(s,sub(u,t))
def touching(p,q):
 F,G=faces(p),faces(q)
 return [k for k in F.keys()&G.keys() if F[k]==-G[k]]
def internal():
 E=set()
 for a in CHILDREN:
  for b in CHILDREN:
   if a!=b and touching(a,b):E.add(normalize(a,b))
 return E
def offspring(edge):
 E=set()
 for a in CHILDREN:
  for b in refinements(edge):
   if touching(a,b):E.add(normalize(a,b))
 return E
def closure():
 E=internal();rounds=[len(E)];history=[]
 while True:
  delta=set().union(*(offspring(e) for e in E))-E
  history.append(sorted(delta))
  if not delta:break
  E|=delta;rounds.append(len(E))
 return E,rounds,history
# For each native face, four quadrants at odd eighth coordinates.
# The chart tangent directions are the remaining world axes in increasing order.
def ports(pose):
 s,t=pose;out={}
 for j,((axis,c2),side) in enumerate(NATIVE_FACES):
  tangent=[i for i in range(3) if i!=axis]
  for q,eta in enumerate(product((-1,1),repeat=2)):
   c4=[2*v for v in c2]
   for a,b in zip(tangent,eta):c4[a]+=b
   world=add(sign(s,tuple(c4)),scale(4,t))
   key=(axis,world)
   assert key not in out
   out[key]=(4*j+q,s[axis]*side)
 return out
def relations(E):
 F=ports(ROOT);rows=set()
 for e in E:
  G=ports(e)
  for k in F.keys()&G.keys():
   a,na=F[k];b,nb=G[k];assert na==-nb
   rows.add((min(a,b),max(a,b),-1))
 return rows
def kernel(n,rows):
 adj=[[] for _ in range(n)]
 for a,b,s in rows:adj[a].append((b,s));adj[b].append((a,s))
 comp=[];visited=set();profile=[0]*n
 for start in range(n):
  if start in visited:continue
  sigma={start:1};stack=[start];bad=False
  while stack:
   a=stack.pop();visited.add(a)
   for b,s in adj[a]:
    v=s*sigma[a]
    if b in sigma:bad|=sigma[b]!=v
    else:sigma[b]=v;stack.append(b)
  comp.append({'signs':sigma,'balanced':not bad})
 k=0
 for c in comp:
  if c['balanced']:
   k+=1
   for a,s in c['signs'].items():profile[a]=k*s
 return comp,profile
if __name__=='__main__':
 import json,time
 from pathlib import Path
 start=time.monotonic();E,r,h=closure();rows=relations(E);comp,a=kernel(4*len(NATIVE_FACES),rows)
 S=[cells(c) for c in CHILDREN];assert len(set().union(*S))==56==sum(map(len,S))
 target={tuple(2*x[i]+b[i] for i in range(3)) for x in P for b in BITS};assert set().union(*S)==target
 out={'substitution_children':CHILDREN,'contact_round_counts':r,'contact_states':sorted(E),'native_faces':NATIVE_FACES,'signed_rows':sorted(rows),'kernel_dimension':sum(c['balanced'] for c in comp),'component_sizes':[(len(c['signs']),c['balanced']) for c in comp],'maximal_profile':a,'seconds':time.monotonic()-start}
 Path(__file__).resolve().parents[1].joinpath('results/chair_closure.json').write_text(json.dumps(out,indent=2))
 print({k:v for k,v in out.items() if k not in ['contact_states','signed_rows','native_faces','maximal_profile']})
