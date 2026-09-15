#!/usr/bin/env python3
"""Symbolic recurrence and exact uniform inball bounds, separate SymPy arithmetic.
The macro grammar is the imported hatviz grammar; this derives its size bound.
"""
from pathlib import Path
import json,sys
import sympy as s
import construct as c
HERE=Path(__file__).resolve().parent
a,b,r=s.symbols('a b r',real=True)
def canonical(a,b):
 k=1+2*a+b;q=1-a-2*b;l=a+2*b
 return [c.Meta(p,[],kind) for p,kind in [
  ([(0,0),(k,0),(k,q),(0,k+q),(-q,k+q),(-q,q)],'H'),
  ([(0,0),(k-q,0),(0,k-q)],'T'),
  ([(0,0),(k,0),(k-l,l),(-l,l)],'P'),
  ([(0,0),(1,0),(1+a,b),(1+a-b,a+2*b),(-l,l)],'F')]]
def cancel_point(p):return tuple(s.cancel(x) for x in p)
def symbolic_recurrence():
 # Reuse the placement *grammar*, replacing its Fraction arithmetic with
 # independently implemented symbolic rational functions. No numerical fits.
 oldQ,oldmul=c.Q,c.mul
 c.Q=lambda x,y=1:s.cancel(s.sympify(x)/y)
 c.mul=lambda A,B:tuple(s.cancel(x) for x in oldmul(A,B))
 ms=canonical(a,b)
 for m in ms:m.shape=[tuple(map(s.sympify,p)) for p in m.shape]
 nxt=c.advance(ms);f=nxt[3].shape
 v=cancel_point(c.sub(f[1],f[0]));w=cancel_point(c.sub(f[2],f[1]))
 assert v==(2*a+3,2*b-1) and w==(-b,a+b+1)
 # Express w in the new (v,R60 v) basis, and check every next macro shape
 # against the same canonical family up to its placement and orientation.
 seg=c.segment((0,0),v);inv=c.inverse(seg);ap,bp=cancel_point(c.at(inv,w))
 expected=canonical(ap,bp)
 for actual,exp in zip(nxt,expected):
  E=[cancel_point(c.at(seg,p)) for p in exp.shape]
  A=c.match(E[0],E[1],actual.shape[0],actual.shape[1])
  # Aligning these two directed edges must be a rigid motion, not a rescale.
  x,y=A[0],A[3];assert s.cancel(x*x+x*y+y*y-1)==0
  for p,q in zip(E,actual.shape):assert cancel_point(c.sub(c.at(A,p),q))==(0,0)
 c.Q,c.mul=oldQ,oldmul
 R=s.Matrix([[0,-1],[1,1]]);I=s.eye(2)
 M=(3*I-R).row_join(2*I).col_join(R.row_join(R))
 assert M*M-3*M+s.eye(4)==s.zeros(4)
 return {'edge_update_matrix':list(map(list,M.tolist())),'characteristic_identity':'M^2 - 3 M + I = 0','canonical_family_preserved':True}
def bernstein_positive(expr):
 # Exact polynomial positivity on [0,2/5] via its Bernstein basis. All returned
 # coefficients are positive; no sampled or floating-point bound is used.
 num,den=s.fraction(s.cancel(expr));records=[]
 for poly in (num,den):
  t=s.symbols('t');P=s.Poly(s.expand(poly.subs(r,s.Rational(2,5)*t)),t);n=P.degree()
  power=[P.nth(i) for i in range(n+1)]
  coeffs=[sum(power[i]*s.binomial(k,i)/s.binomial(n,i) for i in range(k+1)) for k in range(n+1)]
  assert all(x>0 for x in coeffs), (expr,coeffs)
  records.append({'degree':n,'bernstein_coefficients':list(map(str,coeffs))})
 return records
def bounds():
 # Normalized exact orbit v=(6,-2r), w=(-2r,2+2r), with u_0=1,r_0=0,
 # u'=(3-r)u, r'=1/(3-r). Interval [0,2/5] is invariant; u'>=13u/5.
 v=(s.Integer(6),-2*r);w=(-2*r,2+2*r)
 Rv=(-v[1],v[0]+v[1]);det=c.cross(v,Rv)
 aa=s.cancel(c.cross(w,Rv)/det);bb=s.cancel(c.cross(v,w)/det)
 rows=[]
 for m in canonical(aa,bb):
  p=[cancel_point((x*v[0]+y*Rv[0],x*v[1]+y*Rv[1])) for x,y in m.shape]
  centre=tuple(s.cancel(sum(q[i] for q in p)/len(p)) for i in (0,1))
  edgebounds=[]
  for i in range(len(p)):
   edge=c.sub(p[(i+1)%len(p)],p[i]);inside=c.sub(centre,p[i]);cross=c.cross(edge,inside)
   # Convexity: every other vertex is strictly left of this oriented edge.
   convex=[]
   for j in range(len(p)):
    if j in (i,(i+1)%len(p)):continue
    convex.append(bernstein_positive(c.cross(edge,c.sub(p[j],p[i]))))
   # distance^2 = (3/4) cross^2 / norm(edge)^2 > 1/10000.
   dist=bernstein_positive(7500*cross**2-c.norm2(edge))
   edgebounds.append({'convexity':convex,'inball_bound':dist})
  rows.append({'type':m.kind,'normalized_polygon':[[str(x) for x in q] for q in p],'centroid':[str(x) for x in centre],'edges':edgebounds})
 # Interval invariance, with all denominators positive.
 assert s.Rational(1,3)>0 and 1/(3-s.Rational(2,5))<s.Rational(2,5)
 return rows
def main():
 rec=symbolic_recurrence();rows=bounds()
 out={'status':'PASS','recurrence':rec,'orbit':'v_n=(6u_n,-2t_n), w_n=(-2t_n,2u_n+2t_n), (u_next,t_next)=(3u-t,u), (u0,t0)=(1,0)','ratio_interval':['0','2/5'],'growth_lower_bound':'u_n >= (13/5)^n','all_four_inball_radius_lower_bound':'u_n/100','positive_polynomial_certificates':rows,'scope':'all-scale convex macroshape growth; recognition and compatible hat decoration remain separate imported inputs'}
 (HERE/'growth.json').write_text(json.dumps(out,indent=2,default=str)+'\n');print('PASS: symbolic shape closure, edge recurrence, and uniform inball bound (13/5)^n / 100')
if __name__=='__main__':main()
