# R004 — anti-symmetry across a tower with varying geometry

Reference inspection revealed a significant restriction in the initial plan:
the hat's original macrotiles change shape between generations. Its hierarchy
is combinatorially stable without a stationary finite list of geometric shapes.
Requiring one endomorphism of a fixed geometric tiling space would impose an
unnecessary construction obligation.

A derived SBT endpoint removes that restriction. This is an elementary extension
of the period-transport argument, not a claim of a new general aperiodicity
mechanism or a claim that any desired tower exists.

## Geometric theorem

For n>=0 let Y_n be classes of tilings by bounded full-dimensional sets, with
every tile in every Y_n containing an open inball of radius at least r_n>0.
Let D_n:Y_n -> Y_(n+1) be defined on every member and translation-equivariant.
Assume r_n is unbounded and Y_0 is nonempty. Then every member of Y_0 has
trivial translation stabilizer.

Proof. A nonzero period v of a tiling also periods D_(n-1)...D_0 of that tiling.
In any tiling in Y_n, a tile Q and Q+v are distinct because Q is bounded. Their
open inballs have center displacement v, so nonoverlap gives |v|>=2r_n. This
cannot hold for all n if r_n is unbounded. QED.

The same proof allows D_n(T+v)=D_n(T)+B_n v, with invertible linear B_n,
provided for every nonzero v some n satisfies

    |B_(n-1)...B_0 v| < 2r_n.

Constant-scale expansive deflation and unscaled growing macrotiles are two
instances. The geometric scale and the transport may vary together; only their
relative separation matters. Nonemptiness remains a separate input.

## Why the extension matters for construction

Do not require exact metric recurrence when a coherent sequence of geometric
representations preserves the same local incidence/recognition laws. The return
needs all-level covariant grouping, closure into the next legal class, and the
size bound. A list of unrelated drawings does not satisfy those obligations.
Coarse cells can be built using audited boundary cuts; they need not group only
whole physical tiles, if cuts are canonical, disjoint and compatible.

The R001 periodic chair control cannot satisfy this theorem's hypotheses: any
proposed tower of arbitrarily large inball cells over its periodic tiling must
lose equivariance, legal closure, or the growth condition. This supplies a
concrete falsification control, not a vacuous declaration of success.

## Formal scope

formal/Tower.lean proves period transport and anti-symmetry for a dependent
sequence of level types, with an abstract natural-valued displacement height
and independently supplied minimum-period bounds. The geometric inball argument
and the hat's actual grouping/growth are prose inputs, not formalized geometry.
The real/vector generalization above is proved in prose; the current Lean file
covers the unchanged-period version. This is suitable for a new SBT theorem
adapter after the current calibration, with scope retained.

3D transfer is direct: the theorem is dimension-independent, while full-
dimensional inball growth rules out a hidden unexpanded direction. Screw
exclusion still requires the finite-orientation or recognized-lattice bridge.
