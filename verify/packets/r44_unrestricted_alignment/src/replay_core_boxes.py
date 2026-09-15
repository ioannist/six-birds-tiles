#!/usr/bin/env python3
"""Independent integer replay of every exported physical collision box.

This deliberately does not import verify_alignment.py. It verifies the positive
volume witnesses; completeness of the mate quantifier is checked separately by
verify_alignment.py. Coordinates here are integers in units of 1/400.
"""
from pathlib import Path
from itertools import product
import gzip, json, time
from functools import lru_cache

BASE=Path(__file__).resolve().parents[1]
CELLS=tuple(x for x in product((0,1),repeat=3) if x!=(1,1,1))

def check(c,msg):
    if not c: raise ValueError(msg)

@lru_cache(None)
def selected_box(g,t,which):
    cell=CELLS[which]
    result=[]
    for output in range(3):
        source=next(j for j in range(3) if abs(g[j])==output+1)
        lo=cell[source] if g[source]>0 else -cell[source]-1
        result.append(8*lo+t[output])
    return tuple(result)

start=time.monotonic(); records=0; collisions=0;minimum=None
with gzip.open(BASE/'results/collision_core_witnesses.jsonl.gz','rt') as fh:
    for line in fh:
        r=json.loads(line); records+=1
        g,t=map(tuple,r['normalized_other'])
        seen=set()
        for h,u,ia,ib,claimed_lo,claimed_hi in r['overlaps']:
            h,u=tuple(h),tuple(u)
            check((h,u) not in seen,'duplicate companion in an exported record');seen.add((h,u))
            a=selected_box(g,t,ia); b=selected_box(h,u,ib)
            lo=tuple(max(a[i],b[i]) for i in range(3))
            hi=tuple(min(a[i]+8,b[i]+8) for i in range(3))
            check(lo==tuple(claimed_lo) and hi==tuple(claimed_hi),'incorrect box witness')
            lower400=tuple(50*x+4 for x in lo)
            upper400=tuple(50*x-4 for x in hi)
            widths=tuple(y-x for x,y in zip(lower400,upper400))
            check(min(widths)>=42,'overlap contains no certified retained-core box')
            center400=tuple(25*(lo[i]+hi[i]) for i in range(3))
            for c,low,high in zip(center400,lower400,upper400):
                check(c-low>=21 and high-c>=21,'claimed radius 21/400 not justified')
            minimum=min(widths) if minimum is None else min(minimum,min(widths))
            collisions+=1
check(records==5273 and collisions==299975,'wrong number of physical witnesses')
r={'status':'PASS','rejected_pose_records':records,'physical_collision_boxes':collisions,
   'coordinate_denominator':400,'minimum_box_width_numerator':minimum,
   'each_box_contains_open_Euclidean_ball_radius':'21/400',
   'imports_other_verifier':False,'arithmetic':'integer only',
   'scope':'Checks all exported positive-volume collision boxes. Mate-list completeness is a separate gate.',
   'seconds':time.monotonic()-start}
(BASE/'results/core_box_replay.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
