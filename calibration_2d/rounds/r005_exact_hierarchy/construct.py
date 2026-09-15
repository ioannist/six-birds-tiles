#!/usr/bin/env python3
"""Exact rational port of isohedral/hatviz's macro construction.

Source: Craig S. Kaplan, hatviz, commit recorded in sources/hatviz/provenance.json.
Original construction copyright (c) 2023, Craig S. Kaplan.
BSD-3-Clause terms: sources/hatviz/LICENSE. All coordinates here are twice the
display coordinates, in basis (1,0),(1/2,sqrt(3)/2), so hats have unit scale.
This implements the source grammar; it is not an independent discovered grammar.
"""
from fractions import Fraction as Q
from pathlib import Path
from dataclasses import dataclass
from collections import Counter
import json, math
HERE=Path(__file__).resolve().parent
GEOM=json.loads((HERE.parent/'r003_hat_reconstruction/geometry.json').read_text())
OUTLINE=[(0,0),(-1,-1),(0,-2),(2,-2),(2,-1),(4,-2),(5,-1),(4,0),(3,0),(2,2),(0,3),(0,2),(-1,2)]
I=(1,0,0,0,1,0);RM=(1,1,0,-1,0,0);RP=(0,-1,0,1,1,0);REF=(1,1,0,0,-1,0)
def add(p,q):return (p[0]+q[0],p[1]+q[1])
def sub(p,q):return (p[0]-q[0],p[1]-q[1])
def trans(x,y):return (1,0,x,0,1,y)
def at(A,p):a,b,c,d,e,f=A;x,y=p;return (a*x+b*y+c,d*x+e*y+f)
def mul(A,B):
 a,b,c,d,e,f=A;g,h,i,j,k,l=B
 return (a*g+b*j,a*h+b*k,a*i+b*l+c,d*g+e*j,d*h+e*k,d*i+e*l+f)
def inverse(A):
 a,b,c,d,e,f=A;det=a*e-b*d
 return tuple(Q(x)/det for x in (e,-b,b*f-c*e,-d,a,c*d-a*f))
def segment(p,q):
 u,v=sub(q,p)
 return (u,-v,p[0],v,u+v,p[1])
def match(p,q,r,s):return mul(segment(r,s),inverse(segment(p,q)))
def cross(p,q):return p[0]*q[1]-p[1]*q[0]
def intersect(p,q,r,s):
 u,v=sub(q,p),sub(s,r);t=Q(cross(sub(r,p),v))/cross(u,v)
 return add(p,(t*u[0],t*u[1]))
def around(p,R,q):return add(p,at(R,sub(q,p)))
def area2(p):return sum(cross(a,b) for a,b in zip(p,p[1:]+p[:1]))
@dataclass
class Meta:
 shape:list
 children:list
 kind:str
def initial():
 H=[(0,0),(8,0),(8,2),(0,10),(-2,10),(-2,2)]
 T=[(0,0),(6,0),(0,6)];P=[(0,0),(8,0),(4,4),(-4,4)]
 F=[(0,0),(6,0),(6,2),(4,4),(-4,4)]
 hatsH=[match(OUTLINE[5],OUTLINE[7],H[5],H[0]),match(OUTLINE[9],OUTLINE[11],H[1],H[2]),match(OUTLINE[5],OUTLINE[7],H[3],H[4]),mul(trans(4,2),mul(mul(RP,RP),REF))]
 pair=[trans(2,2),mul(trans(-2,4),RM)]
 return [Meta(H,[(a,None) for a in hatsH],'H'),Meta(T,[(trans(0,2),None)],'T'),Meta(P,[(a,None) for a in pair],'P'),Meta(F,[(a,None) for a in pair],'F')]
RULES=[['H'],[0,0,'P',2],[1,0,'H',2],[2,0,'P',2],[3,0,'H',2],[4,4,'P',2],[0,4,'F',3],[2,4,'F',3],[4,1,3,2,'F',0],[8,3,'H',0],[9,2,'P',0],[10,2,'H',0],[11,4,'P',2],[12,0,'H',2],[13,0,'F',3],[14,2,'F',1],[15,3,'H',4],[8,2,'F',1],[17,3,'H',0],[18,2,'P',0],[19,2,'H',2],[20,4,'F',3],[20,0,'P',2],[22,0,'H',2],[23,4,'F',3],[23,0,'F',3],[16,0,'P',2],[9,4,0,2,'T',2],[4,0,'F',3]]
def patch(metas):
 shapes={m.kind:m for m in metas};children=[]
 def ev(c,i):A,m=children[c];return at(A,m.shape[i%len(m.shape)])
 for r in RULES:
  if len(r)==1:children.append((I,shapes[r[0]]));continue
  if len(r)==4:
   idx,edge,kind,newedge=r;p,q=ev(idx,edge+1),ev(idx,edge)
  else:
   idx,edge,idx2,edge2,kind,newedge=r;p,q=ev(idx2,edge2),ev(idx,edge)
  m=shapes[kind];A=match(m.shape[newedge],m.shape[(newedge+1)%len(m.shape)],p,q)
  children.append((A,m))
 return children
def advance(metas):
 ch=patch(metas)
 def ev(c,i):A,m=ch[c];return at(A,m.shape[i])
 b1,b2=ev(8,2),ev(21,2);rb=around(b1,mul(RM,RM),b2)
 p7,p25=ev(7,2),ev(25,2);ll=intersect(b1,rb,ev(6,2),p7)
 w=at(RM,sub(ev(6,2),ll))
 H=[ll,b1,add(b1,w),ev(14,2),sub(ev(14,2),at(RM,w)),ev(6,2)]
 P=[p7,add(p7,sub(b1,ll)),b1,ll]
 F=[b2,ev(24,2),ev(25,0),p25,add(p25,sub(ll,b1))]
 A=H[2];B=add(H[1],sub(H[4],H[5]));T=[B,around(B,RM,A),A]
 inds={'H':[0,9,16,27,26,6,1,8,10,15],'P':[7,2,3,4,28],'F':[21,20,22,23,24,25],'T':[11]}
 return [Meta(poly,[ch[i] for i in inds[k]],k) for k,poly in [('H',H),('T',T),('P',P),('F',F)]]
def flatten(m,A=I):
 for B,child in m.children:
  C=mul(A,B)
  if child is None:yield C
  else:yield from flatten(child,C)
def norm2(p):x,y=p;return x*x+x*y+y*y
def cell_audit(hats):
 occupied=set();edges=Counter()
 # Each standalone macro has its own translated grid origin. Normalize that
 # common phase before testing the integer Laves translation lattice.
 anchor=inverse(hats[0]);hats=[mul(anchor,A) for A in hats]
 allowed={tuple(v for row in R for v in row) for R in GEOM['grid_orthogonal_matrices']}
 for A in hats:
  a,b,c,d,e,f=A;assert (a,b,d,e) in allowed
  assert all(Q(v).denominator==1 for v in A)
  assert f%2==0 and (c-f)%6==0
  for p in GEOM['kite_polygons_lattice']:
   p=[at(A,v) for v in p];key=frozenset(p);assert key not in occupied;occupied.add(key)
   if area2(p)<0:p.reverse()
   for u,v in zip(p,p[1:]+p[:1]):
    if edges[v,u]:edges[v,u]-=1
    else:edges[u,v]+=1
 boundary=[(u,v) for (u,v),n in edges.items() if n]
 # Pick an interior kite centre nearest the polygon centroid, then measure
 # the exact distance to every exposed edge. The open disk of this radius
 # cannot leave the occupied component or enter any hole.
 vertices=[v for p in occupied for v in p]
 mean=tuple(Q(sum(p[i] for p in vertices),len(vertices)) for i in (0,1))
 centers=[tuple(Q(sum(p[i] for p in poly),4) for i in (0,1)) for poly in occupied]
 center=min(centers,key=lambda p:norm2(sub(p,mean)))
 def distance2(a,b):
  u,w=sub(b,a),sub(center,a);q=norm2(u)
  dot=Q(2*w[0]*u[0]+w[0]*u[1]+w[1]*u[0]+2*w[1]*u[1],2)
  t=max(Q(0),min(Q(1),dot/q));delta=sub(w,(t*u[0],t*u[1]));return norm2(delta)
 radius2=min(distance2(a,b) for a,b in boundary)
 return {'hats':len(hats),'kites':len(occupied),'boundary_edges':len(boundary),'covered_disk_center_in_first_hat_frame':center,'covered_disk_radius_squared':radius2}
def encode(o):
 if isinstance(o,Q):return str(o)
 raise TypeError(type(o))
def main():
 metas=initial();records=[]
 for level in range(5):
  rows=[]
  for m in metas:
   hats=list(flatten(m));audit=cell_audit(hats)
   rows.append({'type':m.kind,'polygon':m.shape,'area2':area2(m.shape),**audit})
  records.append({'level':level,'metatiles':rows});print(level,[(r['type'],r['hats'],round(math.sqrt(float(r['covered_disk_radius_squared'])),3)) for r in rows],flush=True)
  if level==3:
   (HERE/'patch_h3.json').write_text(json.dumps({'basis':GEOM['coordinate_basis'],'hat_boundary':OUTLINE,'hat_transforms':list(flatten(metas[0]))},default=encode)+'\n')
  metas=advance(metas)
 (HERE/'certificate.json').write_text(json.dumps({'status':'PASS','levels':records,'scope':'exact finite physical packing and covered-disk checks; infinite existence and all-tilings recognition require their stated proofs'},default=encode,indent=2)+'\n')
if __name__=='__main__':main()
