# R44: a self-preserving 3D parent grammar and an unrestricted-alignment proof submission

**Research continuation: 6 September 2026.**

## Claim and evidence status

This packet proposes an explicit rational polyhedral 3-ball **R44** that tiles Euclidean three-space by congruent copies, while every such tiling has a finite symmetry group. Reflections are allowed in the problem. The proposal is not restricted to grid-aligned placements: Sections 3–6 supply a new unrestricted-alignment argument.

The finite geometric inventories, complete local enumerations, exact mesh, all induced parent contacts, every feature-angle type in the actual mesh, and all 299,975 forced-companion collision checks have been independently replayed using Python's standard library. The geometric and infinite-space arguments are written proofs, not proof-assistant output. **There has been no external adversarial review or Lean-kernel verification of this new claim. Treat this as a proof submission, not an already established result or a priority claim.**

The central new finite identity is

    admitted fine contacts = admitted rescaled parent contacts = 44.

The preceding supplied construction instead went from 62 fine contacts to 398 unrestricted parent contacts. Its fixed-placement no-go theorem is not contradicted: the native child frames in the present dissection are different.

All constants and coordinates are exact. No bounded periodic search, numerical optimization, or search timeout is used as evidence of universal aperiodicity.

## 1. The carrier, dissection, and explicit solid

Let

    P = union_{a in {0,1}^3, a != (1,1,1)} (a + [0,1]^3).

Thus P is the seven-cube chair, of volume 7. Matrices act on column vectors. Write a frame as (p,s), meaning

    G(x)_i = s_i x_{p_i},

with indices 0,1,2. The eight child poses (G,u) are:

| Child | Permutation p | Signs s | Translation u |
|---|---|---|---|
| 000 | (0,1,2) | (+,+,+) | (0,0,0) |
| 001 | (1,0,2) | (+,+,-) | (0,0,4) |
| 010 | (0,2,1) | (+,-,+) | (0,4,0) |
| 011 | (2,0,1) | (+,-,-) | (0,4,4) |
| 100 | (2,1,0) | (-,+,+) | (4,0,0) |
| 101 | (1,2,0) | (-,+,-) | (4,0,4) |
| 110 | (0,1,2) | (-,-,+) | (4,4,0) |
| central | (0,1,2) | (+,+,+) | (1,1,1) |

Every child is a proper rotation of P, and their 56 unit cubes partition 2P exactly. This identity is verified by sets of integer cell coordinates, not by volume alone. Denote the list of poses by C. Refinement acts by

    (G,t) -> {(GH, 2t+Gu) : (H,u) in C}.

### 1.1 Native feature positions

P has 24 exposed unit-square panels. Order them lexicographically by `(normal axis, doubled center)`, exactly as listed in `results/native_panels.csv`. On each panel use the remaining two coordinate axes, in increasing order, as tangent coordinates. Relative to the panel center, the eight marker centers are

    (-1/8,-1/4), (-1/8,+1/4), (+1/8,-1/4), (+1/8,+1/4),
    (-1/4,-1/8), (-1/4,+1/8), (+1/4,-1/8), (+1/4,+1/8).

There are 192 native feature roles. Each base is an axis-parallel square of half-width

    eta = 1/100.

For role u let a_u be the signed integer in `results/native_panels.csv`, or equivalently `results/r44_solid.json`. The magnitudes are 1 through 12. Replace the planar square by the four triangles joining its boundary to the apex

    center + (a_u/10000) n,

where n is the panel's outward unit normal. Positive a_u is a protrusion and negative a_u is a recess. The rest of the panel remains planar.

This defines **one** unmarked solid Q. The role indices describe the construction; they are not additional matching rules imposed on a tiling.

### 1.2 The signed profile is explicit and non-circular

For reproducibility the profile can alternatively be obtained as follows. Start with every face contact inside the eight-child dissection. Propagate contacts through refinement until closed. The counts are 21 then 30, followed by no new contact. At matched marker centers impose the equality

    a_u = -a_v.

There are 372 distinct equations. Their signed graph has twelve balanced connected components, each with eight positive and eight negative vertices. Order components by their smallest role, put that root positive, assign absolute magnitude j to component j, and transport signs. This yields exactly the explicit 192-entry vector in the solid file. The independent verifier reconstructs this graph from the integer dissection.

### 1.3 The solid is a compact polyhedral 3-ball

The marker squares on one panel are disjoint; their centers have separation at least 1/8 in one tangent coordinate, whereas their side length is 1/50. Each lies more than 1/5 from any panel edge. The largest height is 12/10000, less than eta.

Around each marker take a disjoint normal tube of half-height rho=1/100. If f is its signed square-tent graph, the map

    (u,z) -> (u, z + chi(z) f(u)),
    chi(z)=max(0,1-|z|/rho),

is strictly increasing in z: its slope is at least 1-||f||_infinity/rho > 0. It equals the identity on the tube boundary and sends the original planar interface to the feature. The maps glue to an ambient homeomorphism taking P to Q. Therefore Q is homeomorphic to a closed 3-ball, with connected interior and Q=closure(interior Q).

The exact mesh has 2,138 vertices, 6,408 edges, and 4,272 triangles. It is checked triangle-by-triangle against this construction. Volume is exactly 7: each signed component has equal positive and negative counts, and a square pyramid of signed height h adds signed volume (4 eta^2 h)/3.

Every native unit cube retains its core `[rho,1-rho]^3` translated into that cube. This fact will be used in the alignment proof.

## 2. Preliminary facts about congruent tilings

A tiling consists of congruent copies with disjoint interiors and union R^3. We do not initially restrict their orientations, shifts, or handedness.

Because Q is bounded and contains a ball of fixed positive radius, only finitely many congruent copies in a packing can meet any bounded region. Indeed, their corresponding interior balls lie in a common bounded enlargement and have disjoint interiors. Thus all the local finiteness arguments below follow from the geometry, rather than from an assumed grid.

At a point belonging to several polyhedral tiles, their local tangent cones have disjoint interiors. Their solid angles therefore sum to at most 4 pi, and to 4 pi in a tiling. At a generic point on a fixed tile edge, a perpendicular cross-section is partitioned by the incident wedge sectors. Their angles sum to 2 pi. One may avoid every vertex, every transverse edge intersection, and every face plane meeting the reference line in just one point, among the finitely many neighboring tiles.

These statements do not assume a face-to-face tiling.

## 3. Geometry forces each entire pyramid to have one companion

This is the new unrestricted-alignment lemma. It is the highest-priority target for external review.

### Lemma 3.1. Complete angle list

For a feature of absolute height h_j=j/10000 put t_j=h_j/eta=j/100. Its base-edge angle deviations from pi are

    alpha_j = arctan(t_j),

and its apex-ridge deviations are

    beta_j = arccos(1/(1+t_j^2)).

A protrusion has base dihedral pi+alpha_j and ridge dihedral pi-beta_j. A recess has the complementary signs. Every other genuine edge of Q has dihedral pi/2 or 3pi/2. A flat artificial mesh edge has pi.

All 24 nonzero deviations alpha_1,...,alpha_12,beta_1,...,beta_12 are distinct and less than pi/4.

**Proof.** The face slopes are (0,0), (+/-t_j,0), and (0,+/-t_j). Taking their outward-normal dot products gives the formulas. The construction introduces no other non-flat edge types because feature supports are disjoint and avoid the carrier edges.

Both sequences are strictly increasing. A cross equality alpha_i=beta_j would require

    1 + (i/100)^2 = (1 + (j/100)^2)^2,

or `10000 i^2 = 20000 j^2 + j^4`. The exact checker tests all 144 pairs and finds none. For a hand reduction, divisibility by 10000 forces j=10 among 1,...,12; it would then force i^2=201. The upper bounds follow from t_j<1 and (1+t_j^2)^2<2.

The separate `edge_audit.py` checks every one of the actual mesh's 6,408 edges by exact rational outward-normal calculations. It finds precisely 1,536 feature edges, with 32 instances of each sign of each deviation; no unlisted non-flat angle type occurs. It also checks base-edge squared length 4 eta^2 and ridge squared length 2 eta^2+h_j^2. QED.

### Lemma 3.2. Generic feature-edge points have a complementary feature edge

At every generic point of a feature edge in any tiling, exactly one other tile is incident. Its incident edge is the same feature-edge type and height magnitude, with complementary dihedral angle.

**Proof.** Feature angles are strictly greater than 3pi/4. Three feature sectors would exceed 2pi. Two feature sectors plus any ordinary sector, whose angle is at least pi/2, would also exceed 2pi.

If there were only one feature sector, all the remaining sectors would be multiples of pi/2. They could not cancel its nonzero deviation of magnitude less than pi/4. Hence there are exactly two feature sectors and no others. Their deviations are equal with opposite signs; Lemma 3.1 identifies the same j and the same base/ridge type. The two wedges are complementary, so their edge lines coincide locally. QED.

### Lemma 3.3. Feature partners cannot branch or switch

Every point of a feature edge graph has solid angle strictly greater than 7pi/4 inside its tile.

**Proof.** Locally the tile is the hypograph of a square-tent function, possibly negative, over a flat native panel. Its Euclidean Lipschitz constant is at most L=3/25. Its tangent cone contains the circular cone

    v_normal < -L ||v_tangent||.

The cone has solid angle `2pi(1-L/sqrt(1+L^2))`, greater than 7pi/4 because `63 L^2 = 567/625 < 1`. The bound holds at the apex, base corners, and base edges, including their flat surroundings, because every feature lies strictly inside a native panel. QED.

It follows that three distinct tiles cannot meet at a point that lies on a feature graph of each.

For a fixed root feature edge, the companion supplied by Lemma 3.2 is locally constant outside finitely many exceptional points. If it changed at one of those points, both companion feature edges would have that point in their closures, as would the root feature. This would put three feature tangent cones at the same point, a contradiction. The same argument at the root's apex and base corners makes the companions of all eight edges identical.

### Lemma 3.4. A whole feature is rigidly matched to one opposite feature

Each complete square-pyramid feature of every tile in any tiling coincides with an equal, opposite-polarity feature of one other tile.

**Proof.** By Lemma 3.3 one tile contains, on its feature-edge graphs, the whole connected edge graph of the root pyramid. Distinct features of a tile have disjoint compact edge graphs, so this graph lies in one feature of the companion. The edge types and absolute height agree by Lemma 3.2. There are no collinear continuations through the apex or a base corner of a nonzero-height square pyramid. Each root edge is therefore contained in one companion edge of the same length, and hence equals it. All eight edges, the four base corners, and the apex agree. Complementary base/ridge dihedrals imply opposite protrusion/recess polarity.

A rigid motion matching two such marked-square graphs maps their base-plane normal and square edge directions to one another. Therefore its linear part is a signed permutation of the native coordinate axes. Marker centers are all in `(1/8) Z^3`, so its translation is in `(1/8) Z^3`. This conclusion applies to a pair sharing a feature; no global lattice has yet been assumed. QED.

**Important boundary:** the proof does not infer full-feature matching merely from one matching face normal. It uses edge-sector balance, a solid-angle nonbranching argument, connectedness of the marker graph, and equal edge lengths.

## 4. Exhaustive removal of fractional marker-mate placements

Normalize a tile to native pose (I,0). By Lemma 3.4 a feature companion must have a signed-permutation orientation G and translation

    t = c_u - G c_v,

where c_u,c_v are native marker centers of opposite signed height and opposite transformed panel normal.

This finite formula enumerates **all 6,862** possible rigid feature-mate poses. Translations are stored in eighth units.

### Lemma 4.1. Baseline overlap implies physical overlap on the eighth grid

For two such poses, if their baseline P bodies overlap in positive volume, then the corresponding Q bodies overlap in positive volume.

**Proof.** Baseline cubes have side one and corners on the eighth grid. A positive interval overlap has length at least 1/8 in every overlapping coordinate. Eroding each cube by rho=1/100 leaves positive overlap because `2rho<1/8`. These eroded cubes are retained in Q. QED.

This removes all but **5,317** raw mates. Of those, **5,234** have some nonintegral translation coordinate.

### Lemma 4.2. Forced-companion elimination leaves exactly the registered 44 mates

Every feature companion in any global tiling is one of the 44 integral poses in `candidate_certificate.json`.

**Finite proof.** For each of the 5,273 other nonoverlapping mates V, the certificate names a feature u of either the root U or V. Normalize its owner to (I,0). Enumerate *every* possible complete-feature companion W of u using the 6,862-pose inventory and discard only those whose baseline overlaps the owner's baseline.

The options are nonempty for each exhibited feature. Nevertheless every option W has positive-volume baseline overlap with the other tile of the pair. By Lemma 4.1 none can coexist with that tile. The other tile is not itself a possible companion for u. Thus a tiling containing U and V cannot supply the companion that Lemma 3.4 requires.

There are exactly **299,975** such companion collision checks. The independent checker rebuilds the complete companion options and checks each overlap using exact integer boxes. It does not trust the discovery script's stronger-looking flat-panel matching filter.

The 44 survivors have integral translations and are exactly the legal 44-contact atlas independently derived from the actual boundary profile. QED.

This proof requires no assertion that a partial flat contact must already match an entire panel. A missing recess filler is not called impossible merely because it leaves a gap; every possible filler is exhibited as colliding with the other whole tile.

## 5. Pairwise marker alignment implies global registration

### Theorem 5.1. Every tiling by Q is globally grid-registered

Up to one common ambient isometry, all copies in any Q-tiling have signed-permutation orientations and integer translations. Moreover all relative orientations are proper.

**Proof.** Choose any root tile and take the connected component of the undirected graph whose edges join complete marker companions. Lemma 4.2 puts every relative displacement in this component on the integer grid and every relative orientation in the proper cubic group.

The baseline P bodies of distinct component tiles have disjoint interiors by their retained cube cores. Let W be the set of unit grid cells occupied by these bodies. It is nonempty.

If a cell of W has a face neighbor outside the same baseline chair, that exposed unit panel carries eight features. Pick one. Its companion is in the same component and has an integral grid pose. The coincident marker centers lie strictly inside their native unit panels; two integral-grid unit panels sharing that point and plane must be the same panel. The companion therefore owns the unique adjacent unit cell across it. Hence W is closed under all face-neighbor steps in Z^3, and W=Z^3.

Thus the component's baseline bodies tile the grid. Every boundary marker matches its companion, and each shared unit panel has one owner on each side; consequently the component's Q bodies tile all of R^3 by the disjoint-tube argument of Section 1.3. No other positive-volume Q-copy can remain outside the component. This proves global registration, without assuming the original tiling was face-to-face or belonged to a common lattice. QED.

The geometry is chiral in a tiling-relative sense: the raw candidate list included all 48 orientations, but the 44 surviving contacts are proper. A global reflection of a tiling is allowed; mixing its two handedness sectors is not.

## 6. The complete registered local rule

With global registration established, the remainder is finite combinatorial geometry plus a scale argument.

For a normalized root, every adjacent baseline tile covers one of the 22 neighboring grid cells. For each of the 48 orientations, subtract each of its seven cell coordinates from each shell cell, deduplicate, and reject baseline overlaps. There are 2,388 possible face-neighbor poses.

The exact geometric profile admits precisely 44. Every component uses a distinct nonzero magnitude, so checking paired marker-center heights introduces no accidental equalities. The square-pyramid shape is invariant under the tangent square symmetries, so equality of centers, outward normals and opposite heights is equality of the entire local profile, not sampling of an unknown function.

The allowed 44 contacts use 19 distinct relative rotations and generate the entire 24-element proper cubic rotation group. This is different from the eight-element frame group of the previous construction.

### Native asymmetry

Q has no nontrivial self-isometry. The nine large planar boundary components recover the three coordinate directions and the planes at 0,1,2. Their planar areas distinguish the outer area-four, outer area-three and notch area-one regions. The total area of all non-axis pyramid facets is less than 1/4, whereas each of the nine indicated planes carries planar boundary area greater than 9/10. Thus these are precisely the planes carrying boundary area greater than 1/4; the tiny facets cannot replace them under an isometry. The bare P carrier is therefore recovered. Its only native symmetries are the six coordinate permutations. Exact comparison of the 192 features leaves only the identity.

This is important: physical copy frames used in the parent recognizer are not redundant labels invisible in the solid.

## 7. Every legal tiling has a unique parent

For each of the eight children in C there is one candidate parent through a normalized root: apply the inverse child pose to C. Each such cluster has baseline support a congruent copy of 2P.

### Finite first-shell lemma

Enumerate all ways to cover the root's 22 shell cells using the 44 legal whole-tile neighbors, forbidding both whole-body overlaps and illegal contacts between chosen neighbors. There are exactly **33** arrangements. Each contains the face-adjacent sibling signature of exactly one candidate parent.

The independent verifier uses a set-based recursion instead of the generator's memoized bitmask recursion and reproduces all 33 arrangements. These are necessary local configurations, not claims of individual global extendability.

### Central-completion lemma

One of the 33 arrangements makes the root the central child, and it contains all seven outer children. In the other 32, the proposed parent center is already present as a neighbor. Check every one of the 33 possible first shells at that center, retaining every completion compatible with the original whole-tile arrangement.

- 18 outer-root arrangements have no compatible central shell and cannot occur globally.
- 14 have completions; every such completion makes the proposed center genuinely central.
- There are no completions with an incorrectly typed center.

Thus each globally occurring tile belongs to a complete eight-copy parent. All 28 pairs of distinct candidate parents through one root conflict geometrically. Hence two parents cannot share a tile.

### Theorem 7.1. Unique intrinsic partition

Every Q-tiling partitions uniquely into the C parent clusters. The grouping is determined by a finite neighborhood of each tile.

**Proof.** Global registration supplies the complete local inventory. The first-shell lemma proposes a unique parent. The central-completion lemma supplies all its children in every global tiling. The pair-conflict check makes those local assignments globally disjoint and consistent. Every tile is included. QED.

## 8. The parent rule is exactly the same rule

Recognition alone was not enough in the preceding packet. Here we explicitly compute the induced parent language.

A fine legal contact and a choice of participating child in each parent determine their relative macro-pose. Enumerating all `8 x 44 x 8` possibilities and deduplicating gives **697** candidates. Do not assume even translations before checking.

Of these, **116** have disjoint macro-bodies. Testing every fine cross-contact leaves **44** legal macro-contacts. Every admitted translation is even. Dividing translations by two yields *exactly the original 44-pose fine atlas*, not merely an equally sized set:

    rescaled admitted macro-atlas = admitted fine atlas.

### Theorem 8.1. Admissibility-preserving coarsening

Let D partition a Q-tiling into its unique parents, divide the parent origins and scale by two, and replace each parent's standardized chair carrier by a fresh native copy of Q in that frame. Then D(T) is again a Q-tiling.

**Proof.** The macro-bodies partition space. Their contact graph is connected, so the even relative origins imply a common scale-two lattice phase. Every rescaled macro-contact belongs to the same fine atlas. The small-collar realization lemma turns the decoded baseline tiling into a tiling by Q. QED.

D is translation-covariant with scale:

    D(T+v) = D(T) + v/2.

No external phase selector is required: use the actual parent origins divided by two, not a chosen canonical reduction modulo the grid.

D is **not** literal homothety of each cluster's corrugated exterior into Q. It decodes the carrier and restandardizes the surface using the same admissible geometric rule. The earlier Hausdorff-contraction obstruction to an exact self-replicating corrugated macroshape is therefore irrelevant.

## 9. Nonempty global realization

All hierarchy contacts lie in the closed 30-state set used to build the profile. Therefore every finite substitution patch is a valid Q packing with matching internal faces.

Two refinements contain the same-frame grandchild (I,(2,2,2)). This follows directly from the central child (I,(1,1,1)) and its 000 child. Define

    c_n = 2(4^n-1)/3,
    A_n = sigma^{2n}(P) - c_n(1,1,1).

The grandchild relation gives A_n as a literal subpatch of A_{n+1}, with the same native frames. Their supports contain

    [-c_n, (4^n+2)/3]^3.

These cubes exhaust R^3. Hence the nested union supplies a whole-space registered baseline tiling. Its local contacts lie in the closed hierarchy language. Replacing every copy by Q produces a whole-space tiling through the disjoint boundary-tube homeomorphism.

This is an explicit infinite construction. Nonemptiness is not assumed to make the aperiodicity statement nonvacuous.

The executable controls check the same-frame grandchild, exact dissection, and the first two nested patches (64 and 4,096 tiles). The all-n conclusion is the induction above, not a claim based on those finite counts.

## 10. Universal aperiodicity and finite full symmetry

### Proposed Theorem 10.1. Q is a strong 3D Einstein tile

The rational solid Q specified in this packet is a compact polyhedral 3-ball that admits tilings of R^3 by congruent copies. For every such tiling T,

    Per(T) = {0},
    |Sym(T)| <= 24.

Rotations and reflections are permitted when forming a tiling.

**Proof.** Nonemptiness is Section 9. Every tiling is registered by Theorem 5.1. Suppose p is a translation period. Native asymmetry makes p an integer grid vector, since it takes one uniquely framed copy to another.

Theorem 7.1 supplies a translation-covariant intrinsic parent partition, and Theorem 8.1 sends the result back into the same admissible tiling class. Thus p/2 is a period of D(T). Repeating gives p/2^n as a period of a registered Q-tiling for every n. Such a period must again be an integer vector. Hence p belongs to every 2^n Z^3 and is zero.

All copy orientations in a tiling are in one coset of the 24-element proper cubic group. A symmetry's linear part is determined by the image of one native-asymmetric tile and therefore takes at most 24 values. The map from tiling symmetries to their linear parts has kernel equal to the translation symmetries, already proved trivial. Hence it is injective and the symmetry group is finite, of order at most 24. In particular there are no infinite-order screws. QED.

**Submission status:** this is a complete proposed argument with exact finite gates. Its unrestricted feature-partner lemma and the passage from feature components to global registration have not yet received independent human/adversarial review. The Python replay does not constitute a proof-assistant verification of these continuous-geometric lemmas.

## 11. A parameter family, with exact open conditions

The integer heights are a convenient explicit member, not a requirement for the signed graph. Let the twelve component heights be real numbers c_1,...,c_12 near 1,...,12, retain the graph signs, and use height c_j/10000. The proof remains valid provided:

1. Every c_j is nonzero and the absolute magnitudes are distinct.
2. With t_j=|c_j|/100, all `1+t_i^2 != (1+t_j^2)^2`.
3. Every t_j<1, every `(1+t_j^2)^2<2`, and `63 max(t_j)^2<1`.
4. The height remains below rho and eta, as already ensured near the specified member.

These are finitely many strict conditions, all satisfied by the explicit vector. The signed contact rule and the finite feature-mate collision geometry are unchanged; only the feature heights vary. Thus, if Theorem 10.1 survives review, it applies to an open twelve-parameter family within this prescribed geometric architecture. This is not stability under arbitrary unrelated perturbations of the boundary.

## 12. How the new framing changes the SBT mechanism

The old successful recognizer had a well-defined, indeed lossless, reverse description whose parent admissibility was weaker. The present finite certificate closes the **admissibility gate**: the decoded parent obeys exactly the same 44-contact rule.

The proper frame group now has 24 elements. A bare chair has eight missing-corner orientations, leaving three native rotational frames per bare footprint. Those frames are physically distinct for Q because its boundary is asymmetric. The relations among those frames are actual solid-solid compatibility data, not marks added by an observer.

This is why the old arbitrary-compact replacement obstruction does not transfer: it required the former fixed framed placement hierarchy. The new child rotations are different. No assertion is made that changing frames always evades that obstruction; 6,561 stationary proper-frame choices were explored and this particular rule was then separately proved.

- **F7:** keep information sufficiency separate from admissibility. The earlier lossless decoder did not preserve its source predicate; the new one does.
- **F12:** the extra distinction is paid for by a different geometric frame carrier. It is not obtained by repainting the old fixed access quotient.
- **F28:** existence, intrinsic parent recognition, and preservation of the parent admissibility law are separate certificates. All three are explicitly addressed here.
- **G11:** scale-based period exclusion is applied only after nonemptiness, intrinsic recognition, and same-law descent are proved.

Exact supplied-source passages and the evidence boundary are in SOURCE_AUDIT.md. The SBT modules are not invoked as substitutes for the new geometric lemmas.

## 13. Reproduction and review priorities

Run `python src/replay.py` with assertions enabled. The replay uses no external package or solver. The principal checker uses integer matrices, while discovery used permutation/sign pairs. It regenerates every necessary inventory, every first-shell cover, every possible central completion, every parent contact, and every rejected marker mate's whole-body collision options.

`src/edge_audit.py` separately derives all dihedral angle classes and feature-edge lengths from the actual exported mesh. `results/verification.json` and `results/edge_audit.json` are actual run outputs.

Most important review targets, in order:

1. Does generic edge-angle balance necessarily supply the complementary feature edge in a non-face-to-face tiling?
2. Does the solid-angle lower bound rule out every possible switch of feature companion, including endpoints and partial matches?
3. Is the full-feature graph rigidity sufficient to restrict each companion to the enumerated eighth-grid poses?
4. Is the forced-companion option enumeration complete, without relying on flat-panel matching by assumption?
5. Does closure of a marker component's baseline cells under all grid face steps force global registration as proved?
6. Are the 33 first-shell configurations and the induced 44 parent contacts complete in their now-justified carrier?

The packet deliberately retains exact coordinates and short replay code so these questions can be audited rather than accepted on trust.
