#!/usr/bin/env python3
"""Check the four rejected two-hat holes by independent cell-complex geometry."""
from pathlib import Path
from collections import defaultdict
import json
HERE=Path(__file__).resolve().parent
d=json.loads((HERE/'geometry.json').read_text())
polys=[list(map(tuple,p)) for p in d['kite_polygons_lattice']]
rows=json.loads((HERE/'neighbours_independent.json').read_text())['placements']
def area2(p):return sum(a[0]*b[1]-a[1]*b[0] for a,b in zip(p,p[1:]+p[:1]))
checks=[]
for row in rows:
 if not row['holes']:continue
 a,b,c,d,e,f=row['matrix']
 union=polys+[[(a*x+b*y+c,d*x+e*y+f) for x,y in p] for p in polys]
 union=[p if area2(p)>0 else p[::-1] for p in union]
 # Build all empty grid kites meeting the finite bounding box. Six kites
 # surround each sixfold centre; vertices derived directly in oblique basis.
 occupied={frozenset(p) for p in union};empty={}
 vs=[v for p in union for v in p];lo=[min(p[i] for p in vs)-8 for i in (0,1)];hi=[max(p[i] for p in vs)+8 for i in (0,1)]
 directions=[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
 for x in range(lo[0],hi[0]+1):
  for y in range(lo[1],hi[1]+1):
   if y%2 or (x-y)%6:continue
   for u,v in directions:
    left=(-v,u+v);right=(u+v,-u)
    p=[(x,y),(x+u+right[0],y+v+right[1]),(x+2*u,y+2*v),(x+u+left[0],y+v+left[1])]
    key=frozenset(p)
    if key not in occupied:empty[key]=p
 edges=defaultdict(list)
 for key,p in empty.items():
  for a,b in zip(p,p[1:]+p[:1]):edges[frozenset((a,b))].append(key)
 graph=defaultdict(set)
 for users in edges.values():
  for a in users:graph[a].update(b for b in users if b!=a)
 remaining=set(empty);components=[]
 while remaining:
  todo=[remaining.pop()];comp=[]
  while todo:
   k=todo.pop();comp.append(k)
   for b in graph[k]&remaining:remaining.remove(b);todo.append(b)
  components.append(comp)
 # The largest component meets the outside of the bounding box. Each other
 # component is a bounded complement component enclosed by the two hats.
 components.sort(key=len,reverse=True)
 holes=components[1:];assert len(holes)==row['holes']==1
 assert all(len(h)<8 for h in holes)
 # Certify that every boundary edge of each reported finite component meets
 # an occupied kite on its other side, rather than the artificial box boundary.
 occupied_edges=defaultdict(int)
 for p in union:
  for a,b in zip(p,p[1:]+p[:1]):occupied_edges[frozenset((a,b))]+=1
 for hole in holes:
  counts=defaultdict(int)
  for key in hole:
   p=empty[key]
   for a,b in zip(p,p[1:]+p[:1]):counts[frozenset((a,b))]+=1
  assert all(occupied_edges[e]==1 for e,n in counts.items() if n==1)
 checks.append({'matrix':row['matrix'],'hole_kite_counts':list(map(len,holes))})
out={'status':'PASS','checks':checks,'scope':'each of the four excluded two-hat contacts traps fewer than eight kites, so cannot occur in a full aligned hat tiling; not a proof of every intermediate search pruning rule'}
(HERE/'holes.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
