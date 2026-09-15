# R002 — frozen exact substitution maps prohibit every boundary repair

Let P be the R001 chair. Four verified isometries satisfy

    2P = union_i (R_i P+t_i).

No distinct nonempty compact set Q satisfies the same equation. This includes
all polygonal, curved, connected or disconnected boundary modifications.

Proof. On nonempty compact subsets of the plane define

    F(K) = union_i (R_i K+t_i)/2.

For compact K,L, every point of a component of F(K) can be paired with a point
of the corresponding component of F(L) within one-half their Hausdorff distance.
The reverse pairing holds too. Thus d_H(F(K),F(L))<=d_H(K,L)/2. If P,Q are
fixed points, their finite Hausdorff distance obeys d_H(P,Q)<=d_H(P,Q)/2, so
it is zero. Since both sets are closed, P=Q. This requires no assumption that
Q's component images have disjoint interiors. QED.

A separate arithmetic verifier reconstructs the four maps, their orthogonality,
the scale2 cover and the common contraction factor. The uniqueness proof above
is a mathematical self-review, not an independent mathematical referee.

The intended repair is therefore saturated in its declared class: changing
only the boundary while preserving those exact maps cannot change any part
of the returned support, much less eliminate its periodic tiling. This does
not exclude changing the maps, introducing contextual macrotypes, or redesigning
the grammar and solid jointly.

SBT lesson: retaining successful upper assembly maps can freeze the lower
object. The repair must change actual operations or the carrier, not append
a desired recognition label. This supplies a concrete carrier-local SatW;
it is not a claim that all planar shape construction is saturated.

3D transfer: identical Hausdorff contraction proof for any finite fixed family
of strict similarities in any dimension. A fixed multi-type graph-directed
system has the analogous uniqueness proof using the maximum of component
Hausdorff distances. Do not try to add forcing features while silently
holding a complete exact contracting realization fixed.
