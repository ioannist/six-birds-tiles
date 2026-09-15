import framed_chair as F
from chair_core import kernel
from itertools import product
import time,json
from pathlib import Path
C0=F.children(0); CYCLE=((1,2,0),(1,1,1))
def twist(C,i,k):
 out=list(C);h,u=out[i]
 for _ in range(k):h=F.mul(h,CYCLE)
 out[i]=(h,u);return tuple(out)
def examine(C,name):
 t=time.monotonic();E,counts=F.close(C);rows=F.rows(E);comp,a=kernel(192,rows)
 out={'name':name,'children':C,'contact_counts':counts,'kernel_dimension':sum(x['balanced'] for x in comp),'component_count':len(comp),'seconds':time.monotonic()-t,'profile':a,'contact_states':sorted(E)}
 print({k:out[k] for k in ('name','contact_counts','kernel_dimension','component_count','seconds')},flush=True)
 return out
out=[]
for i in [7,0,1,2,3,4,5,6]:
 out.append(examine(twist(C0,i,1),f'twist_{i}'))
 (Path(__file__).resolve().parents[1]/'results/single_twists.json').write_text(json.dumps(out))
