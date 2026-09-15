from pathlib import Path
import json,time
from itertools import permutations,product,combinations
from functools import lru_cache
import framed_chair as F
from chair_core import kernel
B=Path(__file__).resolve().parents[1];DIGITS=(0,0,2,2,1,1,0,0)
CYCLE=((1,2,0),(1,1,1));cyc=[F.ID,CYCLE,F.mul(CYCLE,CYCLE)]
C=tuple((F.mul(h,cyc[k]),u) for (h,u),k in zip(F.children(0),DIGITS))
start=time.monotonic();E,closure=F.close(C);rr=F.rows(E);components,profile=kernel(192,rr)
FRAMES=tuple((p,s) for p in permutations(range(3)) for s in product((-1,1),repeat=3))
S=F.cells(F.ROOT);target=sorted({tuple(x[i]+(d if i==a else 0) for i in range(3)) for x in S for a in range(3) for d in(-1,1)}-S)
raw=set();rootports=F.ports(F.ROOT)
for g in FRAMES:
 for t in {F.sub(c,x) for c in target for x in F.cells((g,(0,0,0)))}:
  e=(g,t)
  if not F.cells(e)&S and F.adjacent(F.ROOT,e):raw.add(e)
def match(e):
 q=F.ports(e)
 return all(profile[rootports[k][0]]==-profile[q[k][0]] for k in rootports.keys()&q.keys())
L={e for e in raw if match(e)}
poses=sorted(L);N=len(poses);ix={p:i for i,p in enumerate(poses)};T={c:i for i,c in enumerate(target)}
cover=[sum(1<<T[x] for x in F.cells(p)&set(T)) for p in poses]
opts=[sum(1<<i for i,c in enumerate(cover) if c>>j&1) for j in range(len(T))]
@lru_cache(None)
def compatible(p,q):
 if p==q:return True
 if F.cells(p)&F.cells(q):return False
 return not F.adjacent(p,q) or F.normal(p,q) in L
conf=[sum(1<<j for j,q in enumerate(poses) if j==i or not compatible(p,q)) for i,p in enumerate(poses)]
@lru_cache(None)
def search(todo,avail):
 if not todo:return (0,)
 choices=[opts[j]&avail for j in range(len(T)) if todo>>j&1]
 if 0 in choices:return ()
 best=min(choices,key=int.bit_count);out=[]
 while best:
  b=best&-best;best-=b;i=b.bit_length()-1
  out.extend(b|rest for rest in search(todo&~cover[i],avail&~conf[i]))
 return tuple(out)
sol=sorted(set(search((1<<len(T))-1,(1<<N)-1)))
def transform(p,q):
 g,t=p;h,u=q;return F.mul(g,h),F.add(t,F.act(g,u))
parents=[];centers=[]
for h,u in C:
 g=F.inv(h);t=F.scl(-1,F.act(g,u));pa={transform((g,t),q) for q in C};parents.append(pa);centers.append(transform((g,t),C[-1]));assert F.ROOT in pa
needs=[sum(1<<ix[p] for p in pa if p in ix) for pa in parents]
roleopts=[[r for r,need in enumerate(needs) if m&need==need] for m in sol]
print('atlas',len(raw),len(L),'closure',closure,'kernel',max(profile),'covers',len(sol),'states',search.cache_info().currsize,'role counts',{n:sum(len(z)==n for z in roleopts) for n in range(9)},flush=True)
cases=[];fail=[];dead=[];passed=[]
if all(len(x)==1 for x in roleopts):
 roles=[r[0] for r in roleopts]
 tables=[]
 for q in centers[:-1]:
  wps=[transform(q,p) for p in poses]
  bans=[sum(1<<i for i,p in enumerate(wps) if not compatible(p,s)) for s in [F.ROOT]+poses]
  reqs=[1<<ix.get(F.normal(q,s),N) if s!=q and F.adjacent(q,s) else 0 for s in [F.ROOT]+poses]
  tables.append((bans,reqs))
 for sid,(m,r) in enumerate(zip(sol,roles)):
  if r==7:continue
  bans,reqs=tables[r];ban=bans[0];req=reqs[0]
  for j in range(N):
   if m>>j&1:ban|=bans[j+1];req|=reqs[j+1]
  choices=[j for j,n in enumerate(sol) if not n&ban and n&req==req]
  wrong=[j for j in choices if roles[j]!=7]
  cases.append([sid,req,ban,choices])
  if wrong:fail.append([sid,wrong])
  elif not choices:dead.append(sid)
  else:passed.append(sid)
 print('two-shell',len(passed),len(dead),len(fail),'central',roles.count(7),flush=True)
pair_compatible=[]
for i,j in combinations(range(8),2):
 ps=list(parents[i]|parents[j])
 if all(compatible(a,b) for a,b in combinations(ps,2)):pair_compatible.append((i,j))
print('parent pairs compatible',pair_compatible,flush=True)
# Induced parent contact atlas including slips.
def macro(e):return tuple(transform(e,p) for p in C)
rootbody=set().union(*(F.cells(p) for p in C));top={}
for p in C:
 for key,s in F.faces(p).items():top[key]=(p,s)
candidates=set()
for p in C:
 for e in L:
  qg,qt=transform(p,e)
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
print('parent',len(candidates),no,len(M),'even',even,'fixed',coarse==L,flush=True)
# Native symmetry and generated orientation group.
syms=[]
for perm in permutations(range(3)):
 mp=F.ports(((perm,(1,1,1)),(0,0,0)))
 if all(profile[rootports[k][0]]==profile[mp[k][0]] for k in rootports):syms.append(perm)
group={F.ID};delta={e[0] for e in L}
while not delta<=group:
 group|=delta;delta={F.mul(g,h) for g in group for h in group}
print('symmetries',syms,'group order',len(group),'all proper',all(F.parity(p)*s[0]*s[1]*s[2]==1 for (p,s),t in L),flush=True)
rec={'digits':DIGITS,'children':C,'closure_counts':closure,'contact_states':sorted(E),'signed_rows':sorted(rr),'profile':profile,'balanced_components':components,
 'raw_contacts':sorted(raw),'legal_contacts':poses,'shell_cells':target,'whole_body_conflicts':conf,'solutions':[ [i for i in range(N) if m>>i&1] for m in sol],'enumeration_states':search.cache_info().currsize,
 'parents':[sorted(p) for p in parents],'role_options':roleopts,'central_completion':cases,'central_passed':passed,'central_dead':dead,'central_wrong':fail,'compatible_parent_pairs':pair_compatible,
 'macro_candidates':sorted(candidates),'macro_nonoverlap':no,'macro_legal':sorted(M),'coarse_equals_fine':coarse==L,'macro_alignment_even':even,'native_symmetries':syms,'orientation_group':sorted(group),'seconds':time.monotonic()-start}
(B/'results/candidate_certificate.json').write_text(json.dumps(rec))
print('total seconds',time.monotonic()-start,flush=True)
