#!/usr/bin/env python3
"""Tuple/integer geometric reconstruction of every aligned contact placement.
No author grid, halo, search, or connectivity functions are imported.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import json,hashlib
HERE=Path(__file__).resolve().parent
d=json.loads((HERE/'geometry.json').read_text());polys=[list(map(tuple,p)) for p in d['kite_polygons_lattice']]
P=set(map(tuple,d['boundary_lattice']));allverts=set(p for poly in polys for p in poly)
# A tile interior is a union of kite interiors. The kite grid is fixed here;
# every admitted affine map preserves its translation lattice and orientations.
cellkeys={frozenset(poly) for poly in polys}
matrices=[tuple(map(tuple,R)) for R in d['grid_orthogonal_matrices']]
def mv(R,p):return tuple(sum(a*b for a,b in zip(row,p)) for row in R)
rows=[]
for R in matrices:
 rotated=[[mv(R,p) for p in poly] for poly in polys];vs=set(p for poly in rotated for p in poly)
 bounds=[range(min(p[i] for p in allverts)-max(p[i] for p in vs),max(p[i] for p in allverts)-min(p[i] for p in vs)+1) for i in (0,1)]
 for tx,ty in product(*bounds):
  if ty%2 or (tx-ty)%6:continue
  moved=[[ (x+tx,y+ty) for x,y in poly] for poly in rotated];keys={frozenset(poly) for poly in moved}
  if cellkeys&keys:continue
  shared=allverts & {p for poly in moved for p in poly}
  if not shared:continue
  # Count complement holes by the planar cell-complex Euler characteristic.
  # The union is connected because shared vertices are nonempty. Its triangles
  # and edges form a planar complex, so bounded holes = 1 - (V-E+F).
  union=polys+moved;verts={p for poly in union for p in poly};edges={frozenset((a,b)) for poly in union for a,b in zip(poly,poly[1:]+poly[:1])}
  holes=1-(len(verts)-len(edges)+len(union));assert holes>=0
  rows.append({'matrix':[R[0][0],R[0][1],tx,R[1][0],R[1][1],ty],'holes':holes,'shared_vertices':sorted(shared)})
assert len({tuple(r['matrix']) for r in rows})==len(rows)
out={'status':'PASS','all_aligned_touching':len(rows),'hole_counts':dict(Counter(r['holes'] for r in rows)),'placements':rows,'scope':'complete grid-preserving contact placements by exact polygon-cell geometry; general alignment is a separate theorem','geometry_sha256':hashlib.sha256((HERE/'geometry.json').read_bytes()).hexdigest()}
(HERE/'neighbours_independent.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',out['all_aligned_touching'],out['hole_counts'])
