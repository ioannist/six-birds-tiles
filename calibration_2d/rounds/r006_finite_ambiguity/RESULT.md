# R006 — finite ambiguity can replace a unique hierarchy

The recognition proof suggests a possible overconstraint for 3D: demanding a
unique parent layout. Uniqueness is sufficient, but the period argument needs
less. The following derived extension preserves the useful ambiguity explicitly.
It is elementary finite-orbit mathematics, with no priority claim.

## Theorem: recognition with a controlled number of global choices

Let X be a translation-invariant class of tilings. For each n and T in X,
let C_n(T) be a **nonempty finite set of entire coarse tilings**, defined from T,
such that C_n(T+v) = {Y+v : Y in C_n(T)}. Suppose every coarse tile is bounded,
coarse interiors are disjoint, and every coarse tile contains an open ball of
radius r_n > 0. Suppose |C_n(T)| <= m_n and r_n/m_n is unbounded. Then every
T in X has no nonzero translation period. If X is nonempty this is a nonvacuous
aperiodicity result. The statement holds in every Euclidean dimension.

Proof. If T+v=T, translation by v permutes the finite nonempty set C_n(T).
Choose Y in this set. Its orbit has length k with 1 <= k <= m_n, so Y+kv=Y.
For v nonzero, any bounded coarse tile Q and Q+kv are distinct. Their interiors
are disjoint, so their translated inballs force k|v| >= 2r_n. Consequently
|v| >= 2r_n/m_n for every n, a contradiction. QED.

No factorial bound is needed: use the orbit of one output, not the order of
the permutation of the whole fiber. Compatibility between different levels
is unnecessary for this theorem; each level already transports any period
into a sufficiently large separated structure.

## Scope and controls

The finite bound is on **global choices for the fixed whole tiling**, not the
number of tile labels or choices at each site. Finitely many local choices can
produce infinitely many global layouts and do not satisfy this hypothesis.
Nonemptiness is essential. A proposed relation must be geometrically defined
and equivariant; selecting a privileged origin does not establish that.

For the periodic unit-square tiling, coarse L-by-L square blocks have L^2
possible global offsets. Translation by (1,0) cycles each offset with length L;
the coarse inradius is L/2. Thus radius grows while r/m=1/(2L) decreases.
The theorem correctly refuses to exclude this periodic tiling. The orbit-length
estimate is sharp here: k|v|=2r. control.py checks the complete offset action
for several L, including translations with nontrivial gcd and diagonal periods.

In a 3D stack, enlarging only the two horizontal dimensions leaves the inradius
bounded by half the unchanged layer thickness. The related dimensional control
shows why an area or diameter growth criterion would be unsound.

## SBT interpretation and next use

The richer carrier can retain a finite fiber of lawful readings rather than a
single canonical reading. P5 packages the complete fiber; P3 transports it;
P6 compares geometric separation with the orbit/ambiguity budget. Its descended
anti-periodicity readout is enough even when individual parent identities do
not descend uniquely. This is a direct theorem, not a universal closure claim.

For 3D, first try bounded global recognition ambiguity if uniqueness is hard.
Measure the actual ambiguity growth relative to full-dimensional cell growth.
R004 is the singleton-fiber case. The hat uses the stronger unique-recognition
input, so this extension is available for transfer but is not needed to establish
the known 2D example. Proof is written mathematics with self-review; no claim
that this extension or its geometric application is Lean-formalized.
