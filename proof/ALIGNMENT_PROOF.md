# Unrestricted alignment of the unchanged R44 solid

**Date:** 6 September 2026.  
**Input:** `upstream/einstein_r44_proof_submission.zip`.  
**Exact solid:** `input/r44_solid.json`, SHA256
`f320d7a0c2d784a3eb29f001dc035808f67591d9ea8d3dd45949e66442f0ed55`.

## Result and verification boundary

**Alignment theorem.** Let Q be precisely the solid in the input above. In any covering of R^3 by isometric copies of Q with pairwise disjoint interiors, there is one ambient isometry after which every copy has an integer translation and a proper cubic rotation as its native pose. Every complete feature-companion pose belongs to the 44-pose atlas in `input/candidate_certificate.json`.

Rotations and reflections are allowed initially. No face-to-face, lattice, common-orientation, or connected-contact-graph hypothesis is imposed on the tiling. There is no change to Q.

This note supplies a complete written proof of the continuous-geometric implications, linked to finite statements checked on the actual mesh by a new implementation. It is not a proof-assistant formalization. No independent external review, publication acceptance, or novelty priority is claimed. The previous registered existence and parent-recognition results are replayed rather than silently extended to arbitrary placements. They are needed for the final Einstein corollary, but not for the alignment theorem itself.

The essential improvement over the input's alignment sketch is a **finite disjoint closed-cover argument on a connected feature graph**. It handles exceptional points and feature vertices simultaneously. A second simplification uses equality of total edge lengths to obtain whole-feature equality, eliminating the need for an informal continuation argument through pyramid vertices. The new finite audit derives the features from the mesh, not from their annotation table, and checks actual retained-core collisions.

## 1. Exact geometry and notation

Let

    P = union { a+[0,1]^3 : a in {0,1}^3, a != (1,1,1) }.

P has 24 exposed unit-square panels. On each panel, in its two increasing tangent coordinate directions, use the following offsets from its center:

    (-1/8,-1/4), (-1/8,+1/4), (+1/8,-1/4), (+1/8,+1/4),
    (-1/4,-1/8), (-1/4,+1/8), (+1/4,-1/8), (+1/4,+1/8).

The base half-width of every marker is eta=1/100. A native feature with coefficient a in {+/-1,...,+/-12} has signed height h=a/10000 in the outward normal direction. In local tangent coordinates u=(u_1,u_2) and outward normal coordinate z, its graph is

    z = f_h(u),
    f_h(u) = h max(0, 1 - ||u||_infinity/eta).

In a neighborhood of the closed feature square, Q is the hypograph z<=f_h(u). The remaining local boundary is z=0. All features are nonzero. A positive coefficient creates a protrusion, a negative coefficient a recess.

The 192 coefficients are fixed by the exact input. Their complete list is also recoverable from the actual mesh: connected components of non-axis triangular faces consist of four triangles each, forming 192 square-pyramid side surfaces. The verifier independently recovers their base planes, centers, signed heights, outward normals, and native roles.

Write E(F) for the **closed edge graph** of one such feature: its four square-base edges and its four apex ridges. It is a compact connected graph without isolated vertices.

Use rho=1/100 for the collar and retained-core margin. The greatest height is 12/10000 < rho. The square bases have side 1/50, and distinct centers on a panel differ by at least 1/8 in at least one tangent coordinate. All bases are at least 1/2-1/4-1/100=6/25 from the corresponding panel edges. Their normal tubes of half-height rho are disjoint. Different coordinate panels also have disjoint marker tubes, since the markers avoid panel edges by this larger margin.

The map

    (u,z) -> (u, z + chi(z) f_h(u)),
    chi(z)=max(0,1-|z|/rho),

is the identity on the tube boundary and strictly increasing on every normal line: its two nontrivial slopes are 1+f_h(u)/rho and 1-f_h(u)/rho, both positive. These disjoint maps give an ambient homeomorphism from P to Q. In particular, Q is a compact regular-closed polyhedral 3-ball with nonempty interior. Every native unit cube retains its eroded core a+[rho,1-rho]^3, and in fact this core is contained in int Q.

The imported mesh-to-construction checker was replayed. The new checker independently extracts all 192 feature fans and classifies all 6,408 actual mesh edges, including 1,536 feature edges.

## 2. Preliminary facts for completely arbitrary congruent tilings

### Lemma 2.1 (local finiteness is automatic)

Every packing by congruent copies of Q is locally finite.

**Proof.** Choose a ball of positive radius contained in int Q and carry it by each tile isometry. These balls have pairwise disjoint interiors. If a tile meets a fixed bounded set K, its carried ball lies in a fixed bounded enlargement of K, since Q has bounded diameter. Infinitely many equal positive-volume disjoint balls cannot lie in that enlargement. Thus only finitely many tiles meet K. ∎

No local-finiteness assumption has been inserted into the target.

### Lemma 2.2 (polyhedral cone budgets)

At a point common to finitely many tiles, the interiors of their local tangent cones are disjoint. Hence their solid angles sum to at most 4*pi. In a tiling their union covers all directions and the sum is 4*pi, with boundaries having spherical area zero.

At a generic point of a chosen edge, a perpendicular cross-section is partitioned into planar wedge sectors with angles summing to 2*pi.

**Proof.** A polyhedral set agrees with a translated polyhedral cone in a sufficiently small ball about a point on its boundary. The radius can be chosen simultaneously for the finitely many incident tiles. Any common open cone direction would yield overlapping tile interiors. Nonincident tiles can be kept outside a sufficiently small ball by local finiteness. Coverage gives the second direction. The cone boundaries are finite unions of planar pieces and therefore have zero spherical area. The same argument applies in the perpendicular plane at a generic edge point. ∎

For clarity about the word *generic*, fix a closed root edge and consider the finitely many tiles meeting it or a small bounded neighborhood. Remove their vertices on that edge, intersections with noncollinear edges, and the intersections with face planes not containing the root line. This removes only finitely many points. At every remaining point, an incident tile either has a face containing the line, or an edge collinear with it. Its cross-section is therefore a half-plane or an ordinary dihedral sector. Artificial coplanar mesh edges contribute angle pi. A different tile cannot contain the point in its interior, since Q is the closure of its interior and the root has interior points arbitrarily nearby.

This treats non-face-to-face contacts explicitly: no whole neighboring facet is assumed to coincide with a root facet.

## 3. Angle identification

Put t_j=j/100 for j=1,...,12, and define

    alpha_j = arctan(t_j),
    beta_j = arccos(1/(1+t_j^2)).

### Lemma 3.1 (complete dihedral list)

A positive feature has base dihedral pi+alpha_j and ridge dihedral pi-beta_j. A negative feature has the complementary signs. Every other genuine edge has angle pi/2 or 3*pi/2. Flat triangulation edges have angle pi.

All 24 positive deviations alpha_j and beta_j are distinct and less than pi/4.

**Proof.** The graph facets have slopes (0,0), (+/-t_j,0), and (0,+/-t_j). The corresponding outward-normal dot products give the stated formulas and signs. The normal tube construction changes no carrier edge. Disjoint supports create no additional kinds of intersection edges.

Both deviation sequences are strictly increasing. Equality alpha_i=beta_j, with angles in (0,pi/2), would imply

    1+(i/100)^2 = (1+(j/100)^2)^2,
    10000 i^2 = 20000 j^2 + j^4.

Thus 10000 divides j^4, so 10 divides j. In the permitted range j=10, and then i^2=201, impossible. The upper bounds follow from t_j<1 and (1+t_j^2)^2<2. Both inequalities hold at the largest t_j=3/25. ∎

These are not assumed to describe an idealized bump while ignoring the exported object. The new audit verifies the cosine-squared ratio, oriented side, and length of every actual feature edge, and proves that all remaining mesh edges are flat or have orthogonal normals. It finds 32 edges of each sign for each of the 24 deviations.

### Lemma 3.2 (a generic feature-edge point has exactly one complementary partner)

At a generic point of any feature edge in any Q-tiling, exactly two tiles are incident: the root and one tile whose incident edge has the same base/ridge type and absolute height, with complementary dihedral angle.

**Proof.** Every feature sector is strictly between 3*pi/4 and 5*pi/4. Three feature sectors would exceed 2*pi. Two feature sectors together with any ordinary sector, of angle at least pi/2, would also exceed 2*pi.

There cannot be just one feature sector: its angle is pi plus a nonzero deviation of magnitude less than pi/4, while all the remaining sectors are integer multiples of pi/2. Such a sum cannot be 2*pi. There is at least one feature sector, namely the root's. Therefore there are exactly two feature sectors and no ordinary sectors. Their deviations have opposite signs and equal magnitude. Lemma 3.1 identifies the same feature height and the same edge type. ∎

This argument does not say that *an edge angle by itself forces a full feature*. That conclusion requires the next section.

## 4. Closed-graph companion theorem

### Lemma 4.1 (uniform solid-angle bound on the entire feature graph)

At every point of E(F), including the apex and every base corner, the interior solid angle of its tile is greater than 4*pi/3. For R44 it is in fact greater than 7*pi/4.

**Proof.** The square-tent graph is globally Euclidean-Lipschitz with constant at most L=3/25. This holds at its creases and along the transition to the flat panel as well as on the faces. At any graph point, the tile's interior tangent cone contains

    { (v,w) : w < -L ||v||_2 }.

The solid angle of this circular cone is

    Omega(L) = 2*pi*(1-L/sqrt(1+L^2)).

It exceeds 4*pi/3 exactly when 8L^2<1. Here 8L^2=72/625<1. The stronger bound Omega(L)>7*pi/4 follows from 63L^2=567/625<1. ∎

Only the weaker, much less marginal condition 8L^2<1 is needed below. In particular, three distinct tiles cannot share a point that lies on a feature graph of all three.

### Theorem 4.2 (one tile accompanies the entire connected feature graph)

For each feature F of a root tile R in an arbitrary Q-tiling, there is a unique other tile S such that E(F) is contained in the union of S's feature edge graphs. Moreover E(F) is contained in one feature edge graph of S.

**Proof.** Only finitely many other tiles meet E(F), by Lemma 2.1. For each such tile S, define

    C_S = E(F) intersect (union of all feature edge graphs of S).

Every C_S is closed in E(F), being an intersection of finite unions of compact segments.

They cover E(F). Indeed, the nonexceptional points on the interiors of root edges are covered by Lemma 3.2. Those points are dense in E(F). The finite union of the closed C_S is closed and contains this dense subset, so it contains E(F).

The sets C_S are pairwise disjoint. If a point belonged to C_S and C_T with S different from T, the root, S, and T would each have a feature graph at that point. Lemmas 2.2 and 4.1 exclude their three solid angles.

A connected space cannot be partitioned into two or more nonempty members of a finite disjoint closed cover: each member would also be open relative to the space, as its complement is a finite union of closed members. Thus exactly one C_S is nonempty and C_S=E(F).

The distinct feature graphs within S are disjoint compact sets. Applying the same connectedness argument to E(F) inside their union shows that one feature F' of S contains the whole graph E(F). ∎

This one argument deals with all formerly implicit switching cases: changes at an interior edge point, at a mesh subdivision vertex, at a pyramid apex, at a base corner, or between features of the same companion. It needs neither a face-to-face hypothesis nor a continuation rule assigned by the observer.

### Lemma 4.3 (containment implies equality of the full features)

The features F and F' in Theorem 4.2 have identical closed edge graphs, equal absolute height, and opposite polarity. Their entire triangular surfaces coincide.

**Proof.** Choose a point in the interior of a base edge of F avoiding all vertices of the finite companion graph. At that generic point Lemma 3.2 applies, so F' has the same height j and the same base-edge type.

The total edge length of either feature of height j is

    ell_j = 8*eta + 4*sqrt(2*eta^2+(j/10000)^2).

We already know E(F) is a closed subset of E(F'). If the inclusion were proper, choose a point of E(F') outside E(F). Its positive distance from the closed E(F), and the absence of isolated vertices in E(F'), would give a nonzero subsegment of E(F') outside E(F). Length additivity for finite unions of segments would then give ell_j<ell_j. Therefore the graphs are equal.

In this graph the apex is the unique vertex of degree four; the four base corners have degree three. Equality recovers the base square and apex, and hence the four triangular faces. Complementary base dihedral angles force opposite feature polarity. ∎

This removes the need to assume or infer that a partial overlap of equal-looking edges continues correctly through a vertex.

### Corollary 4.4 (a complete feature match discretizes the relative pose)

Normalize the root tile's pose to (I,0). Every complete feature companion has a cubic signed-permutation matrix G and a translation

    t = c_u - G c_v in (1/8) Z^3,

where c_u,c_v are native feature centers, a_u=-a_v, and n_u=-G n_v.

**Proof.** A rigid motion matching complete pyramid graphs carries their base-square edge directions and base-plane normal onto one another. Those are the native coordinate directions. Its orthogonal part is therefore a signed permutation, including both determinants. The same graph identifies the center. Opposite polarity and equality of the physical apex force opposite outward base normals. All centers have eighth-integral coordinates. ∎

No global alignment has yet been concluded. Only full feature companions have been reduced to a finite list.

## 5. Certified exclusion of fractional companions

Let F0 be the set of all poses given by Corollary 4.4. For each pose, retain the list of root features it can fully accompany. This is constructed directly from the recovered mesh features over all 48 signed permutations.

### Lemma 5.1 (eighth-grid overlaps penetrate retained cores)

If two such baseline P-poses have positive-volume overlap, the corresponding Q-poses have positive-volume overlap. More quantitatively, an overlapping pair of baseline unit cubes gives an open retained-core box with every side at least 21/200 and hence an open Euclidean ball of radius 21/400 inside both Q interiors.

**Proof.** The relevant cube endpoints are eighth-integral. Each positive coordinate overlap therefore has length at least 1/8. Eroding both cubes by rho=1/100 reduces that interval by 2rho, leaving length at least

    1/8 - 2/100 = 21/200.

Both eroded cubes lie in the physical solid interiors. ∎

Let F1 be the poses in F0 whose baseline P does not overlap the root P. Let Partners(u) be **all** poses in F1 matching root feature u. No other rejection is used when constructing these lists.

The exact census is:

| Object | Count |
|---|---:|
| F0: all rigid complete-feature mate poses | 6,862 |
| Direct retained-core collisions | 1,545 |
| F1: isolated nonoverlapping mate poses | 5,317 |
| Noninteger poses in F1 | 5,234 |
| Integer poses in F1 | 83 |
| Further pairs rejected by compulsory-companion collisions | 5,273 |
| Surviving poses | 44 |

### Finite statement 5.2 (universally quantified collision witnesses)

For each of the 5,273 rejected poses V in F1, the certificate specifies a feature u of either the root U or V. In its owner's native coordinates:

1. The other tile of the pair is not a member of Partners(u).
2. Partners(u) is nonempty.
3. Every W in Partners(u) has a positive-volume baseline overlap with the other tile of the pair.

There are 299,975 option collisions in total. The new verifier regenerates F0 and every Partners(u) from the **actual mesh** and checks all three statements. It does not filter companions by the conclusion to be proved. In particular, it uses no flat-panel consistency filter and no already-rejected pose when pruning these option sets.

For every option the new packet exports one explicit pair of overlapping native cube indices and their intersection interval. A second, separate integer-only checker verifies all of those physical core boxes in units of 1/400. Every box has side lengths at least 42/400.

### Lemma 5.3 (only the 44 surviving mates can occur in a tiling)

No rejected pose can be a feature companion in any full tiling.

**Proof.** Suppose U and V occur. The indicated feature u must have a full companion W by Theorem 4.2 and Lemma 4.3. Its pose must belong to Partners(u): the complete-feature rigidity list is exhaustive, and an overlap with its owner is forbidden. It is not merely the other already placed tile. Statement 5.2 says it overlaps that other tile's baseline. Lemma 5.1 upgrades this to an overlap of physical interiors, a contradiction. ∎

The 44 survivors are all integral and all proper. The new verifier compares their exact pose set—not merely its cardinality—with the independently replayed registered 44-contact atlas. They are equal.

This is a bounded local obstruction with a complete geometric carrier theorem. It is not a search for periodic cells, a timeout, a pointwise sample of surfaces, or an inference that a partial face gap cannot be filled by a third tile.

## 6. From one feature component to the whole of space

### Lemma 6.1 (a feature component's baseline cells exhaust the grid)

Choose any root tile in an arbitrary tiling and normalize its pose to (I,0). In the undirected graph connecting full feature companions, let C be the root's component. All its poses have integer translations and proper cubic frames, and its baseline P-bodies tile the complete unit-cube lattice.

**Proof.** Every graph edge has a relative pose from the 44 integral proper mates. Finite compositions preserve those two properties.

Two baseline bodies in C cannot overlap in a cell: their retained physical cores would overlap. Let W be the nonempty set of unit cells occupied by the component's baseline bodies.

Take a cell a in W and a face-adjacent cell b. If b belongs to the same baseline chair, then b is already in W. Otherwise the common face is an exposed native panel of a's chair. Choose any of its eight features. Its full companion belongs to C. Its base normal is opposite, and its center coincides at a point strictly inside an integral unit panel. Two integral unit squares in that coordinate plane whose relative interiors contain this point must be the same square. Thus the companion owns b, so b belongs to W.

Consequently W is closed under every nearest-neighbor lattice step. Connectedness of the unit-cube adjacency graph gives W=Z^3. There is exactly one owner of each cell by the nonoverlap already proved. ∎

### Lemma 6.2 (the actual component solids, not just their baselines, cover R^3)

**Proof.** Across every baseline panel shared by distinct component chairs, the adjacent cell has one owner. Each of the eight features on that panel must have its companion in that owner: another owner would duplicate the adjacent baseline cell. Thus the two physical profiles agree on the entire panel.

Start with the component's complete baseline grid tiling. Around each paired marker take its closed normal tube of half-height rho, choosing one physical orientation for that tube. On it apply

    H(u,z) = (u, z + chi(z) f(u)).

Opposite native polarity and opposite outward normals give the same physical f on the two sides. This defines one map, not two contradictory maps. The tubes are mutually disjoint except for coincident paired copies, and are locally finite. H is the identity outside them and on their boundaries. Each tube map is a homeomorphism onto itself. These maps glue, with their inverses, to a global homeomorphism H of R^3.

For each component baseline tile G P+t, its image is exactly G Q+t: each of its native boundary edits occurs in the matching tube and no other edit touches its interior core. Hence the component's physical Q-tiles cover all R^3 with disjoint interiors. ∎

### Theorem 6.3 (unrestricted alignment)

Every tiling by Q is globally registered, up to one common ambient isometry. Its relative tile poses use only integer translations and proper cubic rotations.

**Proof.** The component in Lemma 6.2 already fills physical space. An additional tile from a different component would have nonempty open interior. The component tile boundaries form a locally finite union of polyhedral surfaces, so they contain no open ball. Some interior point of the extra tile would lie inside a component tile, violating disjoint interiors. There is therefore no extra component. ∎

This closes the possible loophole of an integral marker network surrounded by tilted or shifted tiles in residual gaps. There are no residual gaps: the tube homeomorphism proves physical coverage, not merely occupancy of an erased grid.

## 7. Consequence for the unchanged registered R44 theorem

The source archive's verifier was rerun from an extracted copy. Its registered statements are:

- the fixed solid has a whole-space tiling, by the stated nested eight-child construction;
- all registered tilings have a unique locally recoverable parent partition (33 complete first shells, all center completions, and all parent conflicts checked);
- the legal parent-contact set, after dividing translations by two, equals the original 44-contact set exactly;
- repeated coarsening rules out nonzero periods;
- Q has no native self-isometry, and its admitted relative frames generate the 24 proper cubic rotations.

The proof of alignment above does not use parent recognition or aperiodicity to eliminate unregistered placements. There is no circularity. It uses only Q's finite geometry, the compulsory-feature theorem, and the finite collision certificates. Equality with the registered atlas is checked after the geometric reduction has been established.

Combining Theorem 6.3 with the replayed registered theorem gives the complete written conclusion:

    Omega(Q) is nonempty;
    for every T in Omega(Q), Per(T)={0} and |Sym(T)|<=24.

For the symmetry bound, map a tiling isometry to its linear part. Its kernel consists of translations and is trivial. Since Q has no native symmetry, the image of one chosen tile determines one of at most 24 allowed linear parts. Thus the full symmetry group is finite, including exclusion of irrational screws. A global reflection of a tiling is allowed; mixing handedness sectors is geometrically excluded.

This note strengthens the alignment proof and its verification, not the declared novelty status. The proof remains open to adversarial mathematical review; no acceptance or Lean verification is asserted.

## 8. Proof dependencies and scope safeguards

| Possible loophole | Discharge |
|---|---|
| Infinitely many tiles accumulate at one feature | Equal interior-ball packing proves local finiteness. |
| A generic section accidentally assumes face-to-face contacts | The finite exceptional set explicitly removes vertices and transverse intersections; remaining sectors can include arbitrary flat faces. |
| One angle match is treated as an entire feature match | The finite disjoint closed cover proves one companion for the whole graph; equal total length proves graph equality. |
| A partner changes at a root apex or base corner | Each closed contact set includes its endpoints; three feature cones cannot coexist. |
| One companion supplies pieces from multiple features | Its finite disjoint compact feature graphs cannot split a connected contained graph. |
| A matched normal leaves a free rotation or tangential slide | Equality of the whole square graph fixes both tangent axes and the center. |
| A third tile fills a misaligned pair's remaining recess | Every possible isolated full companion is enumerated and has a retained-core collision. |
| The finite exclusion uses its own answer to prune options | Partners(u) uses only complete-feature matching and overlap with its owner. |
| A registered graph component leaves unregistered gaps | Cell-neighbor closure plus the explicit global tube homeomorphism proves physical coverage. |
| Reflections or screws are excluded by convention | All 48 pair orientations are included; finite orientation and translation arguments give the symmetry conclusion. |
| Exact mathematics is confused with manufacturable tolerances | No noisy-angle, finite-precision fabrication, or robustness theorem is claimed. |
| Internal checks are called external validation | The packet states precisely that the code is separately implemented but not an external review. |

## 9. What has changed from the source packet

The solid and all previous certified combinatorics are unchanged. The source hashes are retained. New work consists of:

1. The self-contained proof above, especially the finite closed-cover companion theorem, equal-length rigidity, explicit exceptional-set treatment, and full global coverage argument.
2. A new feature-extraction and alignment verifier built from the actual triangles using a signed-column frame representation, importing no source program.
3. Explicit retained-core overlap boxes for all 299,975 exclusions, each containing an open ball of radius 21/400, and a separate integer-only replay of those boxes.
4. Mutation controls and clean bundle replay records.

The continuous statements are established by mathematical proofs, not by the execution log. The execution log establishes only the exact finite and geometric data those proofs use.
