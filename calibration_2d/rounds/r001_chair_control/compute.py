#!/usr/bin/env python3
"""Exact cell-cover control: self-subdivision does not force bare aperiodicity."""
from pathlib import Path
from itertools import product
import json
HERE=Path(__file__).resolve().parent
P=frozenset([(0,0),(1,0),(0,1)])
def normalize(cells):
    x=min(a for a,b in cells);y=min(b for a,b in cells)
    return frozenset((a-x,b-y) for a,b in cells)
def orientations():
    out=set()
    for swap,sx,sy in product((False,True),(-1,1),(-1,1)):
        out.add(normalize([(sx*(y if swap else x),sy*(x if swap else y)) for x,y in P]))
    return sorted(out,key=lambda S:sorted(S))
def covers(target):
    candidates=[]
    for oi,S in enumerate(orientations()):
        for dx in range(min(x for x,y in target),max(x for x,y in target)+1):
            for dy in range(min(y for x,y in target),max(y for x,y in target)+1):
                T=frozenset((x+dx,y+dy) for x,y in S)
                if T<=target:candidates.append({'orientation':oi,'offset':[dx,dy],'cells':sorted(T)})
    by_cell={p:[i for i,c in enumerate(candidates) if p in map(tuple,c['cells'])] for p in target};answers=[]
    def go(remaining,chosen):
        if not remaining:answers.append(sorted(chosen));return
        p=min(remaining,key=lambda p:(sum(set(map(tuple,candidates[i]['cells']))<=remaining for i in by_cell[p]),p))
        for i in by_cell[p]:
            T=set(map(tuple,candidates[i]['cells']))
            if T<=remaining:go(remaining-T,chosen+[i])
    go(set(target),[])
    return {'target':sorted(target),'candidates':candidates,'covers':sorted(answers)}
scaled=frozenset((2*x+i,2*y+j) for x,y in P for i,j in product(range(2),repeat=2))
rectangle=frozenset(product(range(3),range(2)))
out={'tile_cells':sorted(P),'orientations':[sorted(S) for S in orientations()], 'scale2':covers(scaled),'rectangle3x2':covers(rectangle)}
assert out['scale2']['covers'] and out['rectangle3x2']['covers']
(HERE/'certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:len(out[k]['covers']) for k in ('scale2','rectangle3x2')})
