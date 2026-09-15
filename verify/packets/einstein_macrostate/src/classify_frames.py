import framed_chair as F
from chair_core import kernel
from itertools import product
import time,json,sys
from pathlib import Path
C0=F.children(0); CYCLE=((1,2,0),(1,1,1));cyc=[F.ID,CYCLE,F.mul(CYCLE,CYCLE)]
counts={};witnesses={};schemes=[];start=time.monotonic();R=F.ports(F.ROOT)
# output every 100 assignments, clear bulky geometric caches periodically
for n,ks in enumerate(product(range(3),repeat=8)):
 C=tuple((F.mul(h,cyc[k]),u) for (h,u),k in zip(C0,ks))
 E,cs=F.close(C);rows=F.rows(E);components,a=kernel(192,rows);dim=sum(c['balanced'] for c in components)
 typ=tuple(a);key=str(dim);counts[key]=counts.get(key,0)+1
 if typ not in witnesses:witnesses[typ]={'digits':ks,'profile':a,'contacts':sorted(E),'children':C,'counts':cs}
 schemes.append({'digits':ks,'dimension':dim,'contact_count':len(E),'profile_id':list(witnesses).index(typ)})
 if n%100==0:
  print(n,counts,'profiles',len(witnesses),'seconds',round(time.monotonic()-start,3),flush=True)
  F.cells.cache_clear();F.faces.cache_clear();F.ports.cache_clear()
 if (n+1)%250==0:
  (Path(__file__).resolve().parents[1]/'results/frame_progress.json').write_text(json.dumps({'n':n+1,'counts':counts,'profiles':list(witnesses.values()),'seconds':time.monotonic()-start}))
(Path(__file__).resolve().parents[1]/'results/frame_classification.json').write_text(json.dumps({'counts':counts,'profiles':list(witnesses.values()),'schemes':schemes,'seconds':time.monotonic()-start}))
print('DONE',counts,len(witnesses),time.monotonic()-start,flush=True)
