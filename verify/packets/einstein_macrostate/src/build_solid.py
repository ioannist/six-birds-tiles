#!/usr/bin/env python3
"""Build one rational ball-like solid admitting the exact framed chair hierarchy."""
from framed_chair import *
from chair_core import kernel
from fractions import Fraction as F
from collections import Counter,deque

def determinant(a,b,c):
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
def make():
 rec=json.loads((B/'results/candidate_certificate.json').read_text());C=tuple(((tuple(g[0]),tuple(g[1])),tuple(t)) for g,t in rec['children']);E,cs=close(C);_,a=kernel(192,rows(E));assert a==rec['profile']
 eta=F(1,100);eps=F(1,10000);V=[];idx={};tri=[];patches=[]
 def vertex(p):
  p=tuple(p)
  if p not in idx:idx[p]=len(V);V.append(p)
  return idx[p]
 def triangle(p,q,r):tri.append([vertex(p),vertex(q),vertex(r)])
 off=[(sx*F(u,8),sy*F(v,8)) for u,v in ((1,2),(2,1)) for sx,sy in product((-1,1),repeat=2)]
 cuts=sorted({F(-1,2),F(1,2)}|{o+t for z in off for o in z for t in(-eta,eta)})
 for fi,((ax,c2),side) in enumerate(NATIVE):
  c=tuple(F(v,2) for v in c2);tangent=[i for i in range(3) if i!=ax]
  def pt(u,v):
   p=list(c);p[tangent[0]]+=u;p[tangent[1]]+=v;return tuple(p)
  def quad(u0,u1,v0,v1):
   pts=[pt(u0,v0),pt(u1,v0),pt(u1,v1),pt(u0,v1)]
   if (-1)**ax!=side:pts.reverse()
   return pts
  holes={(u-eta,u+eta,v-eta,v+eta):k for k,(u,v) in enumerate(off)}
  for u0,u1 in zip(cuts,cuts[1:]):
   for v0,v1 in zip(cuts,cuts[1:]):
    Q=quad(u0,u1,v0,v1);key=(u0,u1,v0,v1)
    if key in holes:
     k=holes[key];apex=list(pt(*off[k]));apex[ax]+=side*eps*a[fi*8+k];apex=tuple(apex)
     patches.append({'role':fi*8+k,'face':fi,'coefficient':a[fi*8+k], 'base':[list(map(str,p)) for p in Q],'apex':list(map(str,apex))})
     for j in range(4):triangle(Q[j],Q[(j+1)%4],apex)
    else:triangle(Q[0],Q[1],Q[2]);triangle(Q[0],Q[2],Q[3])
 edge=Counter();adj=defaultdict(set)
 for t in tri:
  for j in range(3):edge[(t[j],t[(j+1)%3])]+=1;adj[t[j]].add(t[(j+1)%3]);adj[t[(j+1)%3]].add(t[j])
 assert all(n==1 and edge[(j,i)]==1 for (i,j),n in edge.items())
 assert len(V)-len(edge)//2+len(tri)==2
 seen={0};todo=[0]
 while todo:
  for v in adj[todo.pop()]:
   if v not in seen:seen.add(v);todo.append(v)
 assert len(seen)==len(V)
 volume=sum((determinant(*(V[i] for i in t)) for t in tri),F(0))/6
 assert volume==7
 # Geometric disjointness: bases have halfwidth 1/100, heights <=12/10000;
 # distinct same-face patch centers differ in one tangent coordinate by >=1/8.
 assert max(map(abs,a))*eps<eta
 for j,p in enumerate(off):
  assert max(map(abs,p))+eta<F(1,2)
  for q in off[:j]:assert max(abs(p[k]-q[k]) for k in range(2))>2*eta
 out={'name':'R44 self-closing framed chair candidate','status':'R44 proof submission: polyhedral 3-ball with claimed unrestricted strong aperiodicity; finite gates checked; geometric lemmas not externally reviewed',
      'base_unit_cubes':sorted(P),'vertices':[[str(v) for v in p] for p in V],'triangles':tri,'patches':patches,'profile':a,
      'base_halfwidth':str(eta),'height_unit':str(eps),'exact_volume':str(volume),'vertex_count':len(V),'edge_count':len(edge)//2,'triangle_count':len(tri),
      'substitution_children':C,'contact_state_count':len(E),'contact_equations':len(rows(E)),'kernel_dimension':12}
 return out,V,tri
if __name__=='__main__':
 out,V,T=make();(B/'results/r44_solid.json').write_text(json.dumps(out,indent=2))
 with (B/'results/r44_solid.obj').open('w') as f:
  f.write('# R44 candidate. Proof submission: unrestricted strong aperiodicity claimed; external review pending.\n')
  for p in V:f.write('v '+' '.join(f'{float(v):.12g}' for v in p)+'\n')
  for t in T:f.write('f '+' '.join(str(i+1) for i in t)+'\n')
 print({k:out[k] for k in ['vertex_count','edge_count','triangle_count','exact_volume','kernel_dimension']})
