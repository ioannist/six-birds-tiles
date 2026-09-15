from pathlib import Path
import json,time
import framed_chair as F
from itertools import product,permutations
from functools import lru_cache
BASE=Path(__file__).resolve().parents[1]/'results'; D=json.loads((BASE/'frame_progress.json').read_text())
FRAMES=tuple((p,s) for p in permutations(range(3)) for s in product((-1,1),repeat=3))
S=F.cells(F.ROOT);shell={tuple(x[i]+(d if i==a else 0) for i in range(3)) for x in S for a in range(3) for d in(-1,1)}-S
raw=set()
for g in FRAMES:
 for t in {F.sub(c,x) for c in shell for x in F.cells((g,(0,0,0)))}:
  e=(g,t)
  if not F.cells(e)&S and F.adjacent(F.ROOT,e):raw.add(e)
ROOTPORT=F.ports(F.ROOT)
# root/neighbor contact row charts cached across profiles
rowmap={e:[(ROOTPORT[k][0],F.ports(e)[k][0]) for k in ROOTPORT.keys()&F.ports(e).keys()] for e in raw}
outputs=[]
for idx,rec in enumerate(D['profiles']):
 if max(rec['profile'])<5:continue
 st=time.monotonic();a=rec['profile'];C=tuple(((tuple(g[0]),tuple(g[1])),tuple(t)) for g,t in rec['children'])
 L={e for e,pairs in rowmap.items() if all(a[x]==-a[y] for x,y in pairs)}
 syms=[]
 for p in permutations(range(3)):
  f=F.ports(((p,(1,1,1)),(0,0,0)))
  if all(a[ROOTPORT[k][0]]==a[f[k][0]] for k in ROOTPORT):syms.append(p)
 def macro(e):
  g,t=e;return tuple((F.mul(g,h),F.add(t,F.act(g,u))) for h,u in C)
 rootbody=set().union(*(F.cells(p) for p in C));top={}
 for p in C:
  for k,s in F.faces(p).items():top[k]=(p,s)
 candidates=set()
 for h,u in C:
  for eg,v in L:
   qg=F.mul(h,eg);qt=F.add(u,F.act(h,v))
   for r,w in C:
    g=F.mul(qg,F.inv(r));t=F.sub(qt,F.act(g,w));candidates.add((g,t))
 candidates.discard(F.ROOT);M=set();no=0
 for e in candidates:
  ps=macro(e)
  if rootbody&set().union(*(F.cells(p) for p in ps)):continue
  no+=1;edges=set()
  for q in ps:
   for k,s in F.faces(q).items():
    if k in top and top[k][1]==-s:edges.add(F.normal(top[k][0],q))
  if edges and edges<=L:M.add(e)
 even=all(all(x%2==0 for x in t) for g,t in M)
 coarse={(g,tuple(x//2 for x in t)) for g,t in M} if even else set()
 rec2={'profile_index':idx,'digits':rec['digits'],'native_symmetries':syms,'legal_contacts':len(L),'frames':len({g for g,t in L}),'macro_candidates':len(candidates),'macro_nonoverlap':no,'macro_legal':len(M),'all_even':even,'coarse_new':len(coarse-L),'lost':len(L-coarse),'seconds':time.monotonic()-st,'fine':sorted(L),'macro':sorted(M)}
 print({k:v for k,v in rec2.items() if k not in ['fine','macro']},flush=True);outputs.append(rec2)
 (BASE/'profiles_parent_tests.json').write_text(json.dumps(outputs))
