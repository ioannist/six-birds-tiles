#!/usr/bin/env python3
"""Reconstruct the hat's kite polygons and boundary using exact lattice geometry."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import sys,json,hashlib
HERE=Path(__file__).resolve().parent
source=HERE.parents[1]/'sources/validate';sys.path.insert(0,str(source))
from hat import hat,hat_outline
from kitegrid import getSixfoldCentre,R60,R300,orientations

def xy(p):return p.x,p.y
def area2(poly):return sum(a[0]*b[1]-a[1]*b[0] for a,b in zip(poly,poly[1:]+poly[:1]))
kites=[];edges=Counter()
for p in sorted(hat):
 c=getSixfoldCentre(p);v=p-c
 poly=list(map(xy,[c,c+v+R300*v,c+v*2,c+v+R60*v]))
 assert area2(poly)>0;kites.append(poly)
 for a,b in zip(poly,poly[1:]+poly[:1]):
  if edges[b,a]:edges[b,a]-=1
  else:edges[a,b]+=1
boundary={a:b for (a,b),n in edges.items() if n}
assert len(boundary)==sum(edges.values()) and all(n in (0,1) for n in edges.values())
start=min(boundary);poly=[start];q=boundary[start]
while q!=start:assert q not in poly;poly.append(q);q=boundary[q]
assert len(poly)==len(boundary)
# Remove all inessential collinear vertices.
changed=True
while changed:
 changed=False
 for i in range(len(poly)):
  a,b,c=poly[i-1],poly[i],poly[(i+1)%len(poly)]
  if (b[0]-a[0])*(c[1]-b[1])==(b[1]-a[1])*(c[0]-b[0]):poly.pop(i);changed=True;break
outline=list(map(xy,hat_outline));assert len(outline)==len(poly)==13
assert any(poly==outline[i:]+outline[:i] for i in range(len(outline)))
assert area2(poly)==sum(map(area2,kites))
# Exact simplicity: no nonadjacent segment intersections.
def orient(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def on(a,b,p):return orient(a,b,p)==0 and min(a[0],b[0])<=p[0]<=max(a[0],b[0]) and min(a[1],b[1])<=p[1]<=max(a[1],b[1])
def intersect(a,b,c,d):
 o=[orient(a,b,c),orient(a,b,d),orient(c,d,a),orient(c,d,b)]
 return o[0]*o[1]<0 and o[2]*o[3]<0 or on(a,b,c) or on(a,b,d) or on(c,d,a) or on(c,d,b)
for i in range(13):
 for j in range(i+1,13):
  if j in ((i+1)%13,(i-1)%13):continue
  assert not intersect(poly[i],poly[(i+1)%13],poly[j],poly[(j+1)%13])
lengths=[]
for a,b in zip(poly,poly[1:]+poly[:1]):
 x,y=b[0]-a[0],b[1]-a[1];lengths.append(x*x+x*y+y*y)
G=((Q(1),Q(1,2)),(Q(1,2),Q(1)));matrices=[]
for T in orientations:
 a,b,_,d,e,_=T.m;R=((a,b),(d,e))
 assert tuple(tuple(sum(R[k][i]*G[k][l]*R[l][j] for k in range(2) for l in range(2)) for j in range(2)) for i in range(2))==G
 matrices.append(R)
assert len(set(matrices))==12
out={'status':'PASS','coordinate_basis':['(1,0)','(1/2,sqrt(3)/2)'],'boundary_lattice':poly,'kite_polygons_lattice':kites,'twice_lattice_area':area2(poly),'euclidean_area':str(Q(area2(poly),4))+'*sqrt(3)','squared_edge_lengths':lengths,'grid_orthogonal_matrices':matrices,'scope':'exact simple connected polygon reconstructed from eight kites; grid orientation list, not yet a proof all bare tilings align','input_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source/'hat.py',source/'kitegrid.py')}}
(HERE/'geometry.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',out['euclidean_area'],Counter(lengths))
