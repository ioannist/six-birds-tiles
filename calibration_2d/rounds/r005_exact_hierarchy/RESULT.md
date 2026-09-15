# R005 — exact physical patches and an all-scale growth derivation

The author hatviz grammar has been ported to rational arithmetic in the oblique
triangular basis. The original BSD licence and pinned source commit are in
../../sources/hatviz/. The old step115 source files match that snapshot exactly.
This is a new exact implementation of a known construction, not a new grammar.

## Actual bare geometry

construct.py expands the four macrotypes through five levels. Each hat is
checked to be congruent by one of the twelve exact grid isometries. Relative
grid phase is normalized to the first hat: standalone macrotiles have different
origins, so their absolute translation vectors need not share the root grid.
The first draft incorrectly tested absolute phase; its assertion exposed this
coordinate issue and the corrected version checks the common relative grid.

Every placed kite is checked for interior overlap. Boundary edges of the union
are reconstructed; an interior kite centre and exact distances to **all**
exposed edges certify an actual covered disk, including possible hole boundaries.
The H patches contain 4, 25, 169, 1,156 and 7,921 hats. Their certified disk
radii are approximately 2.61, 7.80, 21.02, 52.81 and 136.72. All four macrotypes
pass at every tested level. These finite checks alone are not an infinite proof.

## Exact recurrence, derived symbolically

Let R be rotation by 60 degrees, R(x,y)=(-y,x+y). The first two F-boundary edge
vectors v,w determine the four macroshapes up to rigid placement. In the frame
v=(1,0), write w=(a,b), and set

    k=1+2a+b, q=1-a-2b, l=a+2b.

Canonical polygons are:

    H: (0,0),(k,0),(k,q),(0,k+q),(-q,k+q),(-q,q)
    T: (0,0),(k-q,0),(0,k-q)
    P: (0,0),(k,0),(k-l,l),(-l,l)
    F: (0,0),(1,0),(1+a,b),(1+a-b,a+2b),(-l,l).

growth.py symbolically applies the exact construction, checks the family is
preserved up to rigid motions (including scale exactly one), and derives

    v' = (3I-R)v + 2w,       w' = Rv + Rw.

The four-dimensional block matrix M satisfies M^2-3M+I=0, using R^2-R+I=0.
Consequently both edge vectors obey x_(n+2)=3x_(n+1)-x_n. For the hat's initial
v=(6,0), w=(0,2), the exact orbit is

    v_n=(6u_n,-2t_n),        w_n=(-2t_n,2u_n+2t_n),
    (u_(n+1),t_(n+1))=(3u_n-t_n,u_n),       (u_0,t_0)=(1,0).

Thus r_n=t_n/u_n remains in [0,2/5]: r'=1/(3-r), and
u_(n+1)>=(13/5)u_n. In particular u_n>=(13/5)^n.

## Full-dimensional size, not just edge growth

After factoring out u_n, each of the four polygons is a rational function of
r in the fixed interval [0,2/5]. growth.py proves exact convexity and checks
that the vertex centroid is at distance greater than 1/100 from each edge.
For an edge e and centroid displacement z, squared Euclidean distance to its
line is (3/4)det(e,z)^2/(e_x^2+e_x e_y+e_y^2). Positivity of the claimed bound
and all convexity inequalities is certified by strictly positive Bernstein
coefficients of both numerator and denominator on the entire interval.
growth.json records every rational coefficient. No numerical sampling enters
the all-scale bound. Every macroshape therefore contains an open ball of radius

    (13/5)^n / 100.

The constant is deliberately weak; divergence is what the endpoint needs.

## Imported compatibility and scope

The paper's Section 2 gives compatibility of the hat decorations under this
macro construction; Section 5 proves forced recursive grouping, legal edge and
vertex stars, and symmetry preservation. Its boundary-cut representation is
not literally the straight convex outlines drawn by hatviz. The paper permits
compatible alternative boundaries/whole-tile assignments and supplies the
correspondence. We retain this as an explicit imported bridge rather than
silently identifying different drawings. Section 5 also explicitly establishes
unbounded inball growth for its recognized supertiles. Our derivation supplies
a quantitative growth result for the straight-outline realization.

Infinite nonoverlap/coverage is not inferred solely from five checks. Theorem
2.1's nested-patch extension, or the Section 5 construction and compactness,
provides existence. The final assembly states these inputs exactly. Symbolic
growth is directly checked mathematics; it is not a Lean formalization of hat
geometry. See R004 for the precise scope of the abstract Lean endpoint.
