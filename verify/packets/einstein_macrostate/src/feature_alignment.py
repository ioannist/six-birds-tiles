"""Explore all rigid full-feature mates, including eighth-grid sliding.
This is a finite necessary-pair atlas, not by itself an alignment proof.
"""
import json,time
from pathlib import Path
from itertools import product,permutations
import framed_chair as F
B=Path(__file__).resolve().parents[1];d=json.loads((B/'results/candidate_certificate.json').read_text());a=d['profile'];start=time.monotonic()
G=tuple((p,s) for p in permutations(range(3)) for s in product((-1,1),repeat=3));root=F.ports(F.ROOT)
# All centers and translations below are in units of one eighth.
raw=set();facep={}
for g in G:
 other=F.ports((g,(0,0,0)));facep[g]=other
 for (ax,c),(i,ni) in root.items():
  for (ay,e),(j,nj) in other.items():
   if ax==ay and ni==-nj and a[i]==-a[j]:raw.add((g,F.sub(c,e)))
print('full feature candidates',len(raw),flush=True)
rootboxes=[F.scl(8,x) for x in F.P]
shape={g:[F.scl(8,x) for x in F.cells((g,(0,0,0)))] for g in G}
def overlap(p):
 g,t=p
 return any(all(max(x[i],y[i]+t[i])<min(x[i]+8,y[i]+t[i]+8) for i in range(3)) for x in rootboxes for y in shape[g])
noover={p for p in raw if not overlap(p)}
print('disjoint',len(noover),'nonintegral',sum(any(x%8 for x in t) for g,t in noover),flush=True)
RF=[(ax,F.scl(4,c),s) for (ax,c),s in F.faces(F.ROOT).items()]
faces={g:[(ax,F.scl(4,c),s) for (ax,c),s in F.faces((g,(0,0,0))).items()] for g in G}
# Test all marker centers in each closed overlap of exposed panels.
def panel_contains(axis,center,x):return x[axis]==center[axis] and all(abs(x[i]-center[i])<=4 for i in range(3) if i!=axis)
def passes(p):
 g,t=p;N={(ax,F.add(c,t)):(j,nj) for (ax,c),(j,nj) in facep[g].items()}
 NF=[(ax,F.add(c,t),s) for ax,c,s in faces[g]]
 # Opposing face panels whose interiors overlap.
 panels=[(ax,c,e) for ax,c,s in RF for ay,e,w in NF if ax==ay and s==-w and c[ax]==e[ax] and all(abs(c[k]-e[k])<8 for k in range(3) if k!=ax)]
 for ax,c,e in panels:
  for (az,x),(u,nu) in root.items():
   if az==ax and panel_contains(ax,c,x) and panel_contains(ax,e,x):
    if (az,x) not in N:return False
    v,nv=N[az,x]
    if nu!=-nv or a[u]!=-a[v]:return False
  for (az,x),(v,nv) in N.items():
   if az==ax and panel_contains(ax,c,x) and panel_contains(ax,e,x):
    if (az,x) not in root:return False
    u,nu=root[az,x]
    if nu!=-nv or a[u]!=-a[v]:return False
 return True
passed={p for p in noover if passes(p)}
nonint={p for p in passed if any(x%8 for x in p[1])}
print('compatible',len(passed),'noninteger',len(nonint),flush=True)
if nonint:print('examples',list(sorted(nonint))[:10],flush=True)
old={((tuple(g[0]),tuple(g[1])),tuple(t)) for g,t in d['legal_contacts']}
integers={(g,tuple(x//8 for x in t)) for g,t in passed if all(x%8==0 for x in t)}
print('integer equals old',integers==old,'seconds',time.monotonic()-start,flush=True)
out={'coordinate_scale':8,'raw_feature_mate_count':len(raw),'baseline_disjoint_count':len(noover),'baseline_disjoint_noninteger_count':sum(any(x%8 for x in t) for g,t in noover),'surviving_mates':sorted(passed),'noninteger_survivors':sorted(nonint),'integer_atlas_equals_registered':integers==old,'seconds':time.monotonic()-start}
(B/'results/feature_alignment.json').write_text(json.dumps(out))
