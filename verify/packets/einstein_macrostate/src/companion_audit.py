"""All rejected feature mates have a forced marker-companion collision.
Uses only whole bodies and matching one complete pyramid, not assumptions that
flat panel contacts must themselves match entire decorative patterns.
"""
import framed_chair as F
from collections import defaultdict
from itertools import product,permutations
from pathlib import Path
import json,time
B=Path(__file__).resolve().parents[1];D=json.loads((B/'results/candidate_certificate.json').read_text());a=D['profile'];start=time.monotonic()
G=tuple((p,s) for p in permutations(range(3)) for s in product((-1,1),repeat=3));root=F.ports(F.ROOT);ports={g:F.ports((g,(0,0,0))) for g in G}
shape={g:[F.scl(8,x) for x in F.cells((g,(0,0,0)))] for g in G};R=(F.ID,(0,0,0))
raw=defaultdict(set)
for g in G:
 for (ax,c),(u,nu) in root.items():
  for (ay,e),(v,nv) in ports[g].items():
   if ax==ay and nu==-nv and a[u]==-a[v]:raw[g,F.sub(c,e)].add(u)
def boxes(p):g,t=p;return [F.add(x,t) for x in shape[g]]
boxcache={p:boxes(p) for p in raw};boxcache[R]=boxes(R)
def overlaps(p,q):
 return any(all(x[i]<y[i]+8 and y[i]<x[i]+8 for i in range(3)) for x in boxcache[p] for y in boxcache[q])
noover={p for p in raw if not overlaps(R,p)};options={u:[p for p in noover if u in raw[p]] for u in range(192)}
old=json.loads((B/'results/feature_alignment.json').read_text());passed={((tuple(g[0]),tuple(g[1])),tuple(t)) for g,t in old['surviving_mates']}
RF=[(ax,F.scl(4,c),s) for (ax,c),s in F.faces(F.ROOT).items()]
faces={g:[(ax,F.scl(4,c),s) for (ax,c),s in F.faces((g,(0,0,0))).items()] for g in G}
def inside(ax,c,x):return x[ax]==c[ax] and all(abs(x[i]-c[i])<=4 for i in range(3) if i!=ax)
def witness(p):
 g,t=p;N={(ax,F.add(c,t)):(j,nj) for (ax,c),(j,nj) in ports[g].items()};NF=[(ax,F.add(c,t),s) for ax,c,s in faces[g]]
 for ax,c,s in RF:
  for ay,e,v in NF:
   if ax!=ay or s!=-v or c[ax]!=e[ax] or not all(abs(c[k]-e[k])<8 for k in range(3) if k!=ax):continue
   for owner,(src,dst) in enumerate(((root,N),(N,root))):
    for (az,x),(u,nu) in src.items():
     if az==ax and inside(ax,c,x) and inside(ax,e,x):
      if (az,x) not in dst or nu!=-dst[az,x][1] or a[u]!=-a[dst[az,x][0]]:return owner,u
 return None
out=[];tests=0
for i,p in enumerate(sorted(noover-passed)):
 owner,u=witness(p)
 if owner:
  g,t=p;iv=F.inv(g);test=(iv,F.scl(-1,F.act(iv,t)))
 else:test=p
 assert test in noover
 partners=options[u];assert partners and test not in partners
 for q in partners:
  tests+=1
  if not overlaps(q,test):
   print('FAILED',p,owner,u,q,test,flush=True);raise SystemExit(1)
 out.append({'rejected_pose':p,'marker_owner':owner,'native_role':u,'possible_partners':len(partners)})
 if i%1000==0:print(i,'tests',tests,'seconds',time.monotonic()-start,flush=True)
rec={'status':'PASS','rejected_disjoint_mates':len(out),'companion_collision_tests':tests,'every_blocked_marker_has_partners_in_isolation':True,'every_possible_partner_overlaps_other_tile':True,'witnesses':out,'seconds':time.monotonic()-start}
(B/'results/companion_collision_certificate.json').write_text(json.dumps(rec));print('PASS',len(out),tests,time.monotonic()-start,flush=True)
