"""An alternative proper-rotation realization of the same exact chair dissection."""
from itertools import product,permutations
from functools import lru_cache
from collections import defaultdict
import json,time
from pathlib import Path
B=Path(__file__).resolve().parents[1]
BITS=tuple(product((0,1),repeat=3));P=frozenset(b for b in BITS if b!=(1,1,1))
ID=((0,1,2),(1,1,1));ROOT=(ID,(0,0,0))
def act(g,x):p,s=g;return tuple(s[i]*x[p[i]] for i in range(3))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def scl(n,x):return tuple(n*a for a in x)
def mul(g,h):p,s=g;q,t=h;return tuple(q[p[i]] for i in range(3)),tuple(s[i]*t[p[i]] for i in range(3))
def inv(g):p,s=g;r=tuple(p.index(i) for i in range(3));return r,tuple(s[r[i]] for i in range(3))
def parity(p):return -1 if sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))%2 else 1
def children(mode=0):
 C=[]
 for a in BITS:
  if a==(1,1,1):continue
  s=tuple(1-2*x for x in a)
  if mode==0:p=(1,0,2) if sum(a)%2 else (0,1,2)
  else:
   # fixed deterministic native frame assignments within each determinant class
   perms=[p for p in permutations(range(3)) if parity(p)==(-1 if sum(a)%2 else 1)]
   p=perms[(mode*sum((i+1)*a[i] for i in range(3))+mode//3)%3]
  C.append(((p,s),scl(4,a)))
 C.append((ID,(1,1,1)))
 return tuple(C)
@lru_cache(maxsize=None)
def cells(pose):
 g,t=pose;p,s=g
 return frozenset(tuple(s[i]*b[p[i]]+t[i]-(s[i]<0) for i in range(3)) for b in P)
@lru_cache(maxsize=None)
def faces(pose):
 S=cells(pose);F={}
 for x in S:
  for ax in range(3):
   for d in(-1,1):
    z=list(x);z[ax]+=d
    if tuple(z) in S:continue
    c=tuple(2*x[i]+1+(d if i==ax else 0) for i in range(3));F[(ax,c)]=d
 return F
NATIVE=sorted(faces(ROOT).items())
@lru_cache(maxsize=None)
def ports(pose):
 g,t=pose;p,s=g;out={}
 for a,((ax,c),d) in enumerate(NATIVE):
  ta=[i for i in range(3) if i!=ax]
  offsets=[(sx*u,sy*v) for u,v in ((1,2),(2,1)) for sx,sy in product((-1,1),repeat=2)]
  for k,o in enumerate(offsets):
   z=list(scl(4,c))
   for i,b in zip(ta,o):z[i]+=b
   center=add(act(g,tuple(z)),scl(8,t));wax=p.index(ax);out[(wax,center)]=(8*a+k,s[wax]*d)
 return out

def refined(pose,C):
 g,t=pose;return tuple((mul(g,h),add(scl(2,t),act(g,u))) for h,u in C)
def normal(p,q):
 g,t=p;h,u=q;return mul(inv(g),h),act(inv(g),sub(u,t))
def adjacent(p,q):
 F=faces(p);G=faces(q);return any(F[k]==-G[k] for k in F.keys()&G.keys())
def close(C):
 E={normal(p,q) for p in C for q in C if p!=q and adjacent(p,q)};counts=[len(E)]
 while True:
  nxt=set()
  for e in E:
   for p in C:
    for q in refined(e,C):
     if adjacent(p,q):nxt.add(normal(p,q))
  nxt-=E
  if not nxt:break
  E|=nxt;counts.append(len(E))
 return E,counts

def rows(E):
 F=ports(ROOT);out=set()
 for e in E:
  G=ports(e)
  for k in F.keys()&G.keys():
   a,na=F[k];b,nb=G[k];assert na==-nb
   out.add((min(a,b),max(a,b),-1))
 return out
if __name__=='__main__':
 import sys
 sys.path.insert(0,str(B/'src'));from chair_core import kernel
 results=[]
 for mode in range(7):
  t=time.monotonic();C=children(mode);E,c=close(C);R=rows(E);com,a=kernel(192,R)
  assert set().union(*(cells(p) for p in C))=={tuple(2*x[i]+b[i] for i in range(3)) for x in P for b in BITS}
  assert sum(len(cells(p)) for p in C)==56
  row={'mode':mode,'closure_counts':c,'kernel_dimension':sum(x['balanced'] for x in com),'seconds':time.monotonic()-t,'profile':a,'children':C,'contact_states':sorted(E),'signed_rows':sorted(R)}
  results.append(row);print({k:v for k,v in row.items() if k in ['mode','closure_counts','kernel_dimension','seconds']},flush=True)
 (B/'results/framed_chair_modes.json').write_text(json.dumps(results,indent=2))
