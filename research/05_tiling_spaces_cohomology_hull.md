# Tiling Dynamical Systems, the Continuous Hull, and Topological Invariants

**Research note for the Six Birds monotile track.** Online research; sources cited inline with URLs.
This is the machinery that makes our "inflation-hierarchy-as-a-tower" and "hull-as-stable-inverse-limit"
program a *known* mathematical object rather than a hopeful analogy. The central fact: a substitution
tiling space **is** the inverse limit of a single branched manifold under the inflation map. That is
literally our tower. The strict-extension and cohomological-audit pieces (T1/T2) sit on top of it.

---

## 1. Overview and orientation

A tiling of `ℝᵈ` (e.g. a Penrose tiling, or the shadow of a cut-and-project set) is not studied as one
rigid object. Instead one studies the **space of all tilings locally indistinguishable from it**, equipped
with the `ℝᵈ` translation action. This *tiling dynamical system* `(Ω, ℝᵈ)` is a compact metric space with a
continuous flow, and its topological/dynamical invariants encode exactly the features we care about:
aperiodicity, the forced hierarchy, the diffraction spectrum, and the labels of spectral gaps.

The three layers we will mine, in order:

1. **The hull `Ω`** — orbit closure under translation, with the "big-ball-up-to-small-shift" metric. Its
   dynamical properties (FLC, repetitivity, minimality, unique ergodicity, linear repetitivity) are the
   qualitative skeleton.
2. **The hull as an inverse limit** — Anderson–Putnam: `Ω = ⟵lim(Γ, γ)`, the inverse limit of a single
   branched manifold (the AP complex `Γ`) under the inflation/substitution self-map `γ`. **This is our
   tower / stable inverse limit, made precise.**
3. **Topological invariants** — Čech cohomology `Ȟ*(Ω)` (computed as a direct limit through the AP tower),
   pattern-equivariant cohomology, and the K-theory / gap-labeling of `C(Ω) ⋊ ℝᵈ` (Bellissard). These are
   the *audit* quantities: the cohomology image in `ℝᵈ` and the trace on `K₀` are the eigenvalue/topological
   readouts.

Best single entry points:
- L. Sadun, *Tilings, tiling spaces and topology*, Phil. Mag. 86 (2006) — survey: <https://arxiv.org/abs/math/0506054>
- L. Sadun, *Topology of Tiling Spaces*, AMS University Lecture Series 46 (2008) — the book: <https://books.google.com/books/about/Topology_of_Tiling_Spaces.html?id=dL8FCAAAQBAJ>
- L. Sadun, *Cohomology of Hierarchical Tilings* (2014): <https://arxiv.org/abs/1406.0882>
- L. Sadun, *Introduction to hierarchical tiling dynamical systems* (2018): <https://arxiv.org/abs/1802.09956>

---

## 2. Precise definitions: hull, metric, FLC, repetitivity

### 2.1 Tilings, patches, prototiles

A **tiling** `T` of `ℝᵈ` is a covering of `ℝᵈ` by closed sets ("tiles") with disjoint interiors. Tiles
typically carry a finite set of **prototile** types (shapes up to translation, possibly with labels/markings).
A **patch** is a finite collection of tiles in `T`. The translation group `ℝᵈ` acts on tilings by
`T ↦ T − x` (move the tiling, equivalently move the observer's origin).

### 2.2 The tiling metric (big ball up to a small shift)

The metric formalizes "two tilings are close if they agree on a large region near the origin after a small
adjustment." Sadun's survey states it cleanly:

> *"Two tilings `T₁` and `T₂` are `ε`-close if they agree on a ball of radius `1/ε` around the origin, up to
> a further translation by `ε` or less."*
> — Sadun, *Tilings, tiling spaces and topology*, <https://arxiv.org/abs/math/0506054>

Equivalently, the distance is
```
d(T₁, T₂) = inf { ε > 0 : ∃ x, y ∈ ℝᵈ with |x|,|y| ≤ ε such that
                   (T₁ − x) and (T₂ − y) agree exactly on the ball B_{1/ε}(0) },
```
capped at some `ε_max` (often `1/√2`) so it is a genuine metric. The two small translations `x, y` allow the
patterns to "slide into register"; this is the standard tiling/Gromov–Hausdorff-type metric (see also
Anderson–Putnam, Kellendonk–Putnam). The small-shift slack is exactly why the hull is a *foliated* /
solenoid-like space rather than a Cantor set: locally it looks like (Cantor set in the transverse direction)
× (`ℝᵈ` in the flow direction).

### 2.3 The continuous hull `Ω` (orbit closure)

> *"The space `X_T` is the completion of the orbit of `T` in this metric. Put another way, it is the set of
> tilings `S` with the property that every patch of `S` can be found somewhere in `T`."*
> — Sadun, <https://arxiv.org/abs/math/0506054>

So
```
Ω = Ω_T = closure{ T − x : x ∈ ℝᵈ }   (closure in the tiling metric).
```
It is also called the **continuous hull** or the **local isomorphism (LI) class** of `T`. The `ℝᵈ` action
descends to `Ω`, giving the **tiling dynamical system** `(Ω, ℝᵈ)`. (The word "continuous" distinguishes it
from the **canonical/discrete hull** `Ω₀ = Ω ∩ {tilings with a tile-vertex at 0}`, a Cantor set that is the
transversal to the flow; the discrete hull carries the `ℤᵈ`-style or groupoid dynamics used in K-theory.)

### 2.4 Finite local complexity (FLC)

> *"`T` has FLC when it has only a finite number of tile types, and these tiles fit together in only a finite
> number of ways."*
> — Sadun, <https://arxiv.org/abs/math/0506054>

Equivalently: for each `R`, there are only finitely many patches of diameter `≤ R` up to translation. The
key consequence is **compactness**:

> *"**Theorem.** The tiling space `X_T` is compact if and only if `T` has finite local complexity."*

The mechanism: under FLC any sequence of translates `T − xₙ` has a subsequence converging on every bounded
ball, so the orbit closure is sequentially compact. Compactness is what lets the whole topological-invariant
apparatus (Čech cohomology as a limit of finite complexes, K-theory of `C(Ω)`) run.

### 2.5 Repetitivity (and aperiodicity)

> *"A tiling `T` is **repetitive** if for every patch `P` in `T` there is a radius `R_P` such that every ball
> of radius `R_P` contains at least one copy of `P`."*
> — Sadun, <https://arxiv.org/abs/math/0506054>

Repetitivity is the tiling analogue of an *almost-periodic / uniformly recurrent* point. **Aperiodicity**:

> *"`T` is aperiodic (non-periodic) if there are no vectors `x ∈ ℝᵈ` for which `T = T + x`."*

A repetitive aperiodic FLC tiling is the canonical object of the theory (Penrose, Fibonacci, the
hat/spectre monotiles, cut-and-project sets at irrational slope).

---

## 3. Key dynamical properties

For `(Ω, ℝᵈ)` the translation action, the following hierarchy of properties is standard (Sadun survey;
*Introduction to hierarchical tiling dynamical systems*, <https://arxiv.org/abs/1802.09956>):

- **Minimality.** `(Ω, ℝᵈ)` is *minimal* iff the orbit of every `S ∈ Ω` is dense in `Ω`. **Theorem
  (folklore / Sadun):** `Ω_T` is minimal **iff** `T` is repetitive. Minimality = "every tiling in the hull
  has the same local patches" = local indistinguishability throughout the hull.

- **Unique ergodicity.** `(Ω, ℝᵈ)` is *uniquely ergodic* iff there is a unique `ℝᵈ`-invariant Borel
  probability measure `μ` on `Ω`. For tilings this is equivalent to **uniform patch frequencies**: every
  patch `P` has a well-defined frequency `freq(P)` (number per unit area), with uniform convergence
  independent of where you sample. The invariant measure `μ` *is* the patch-frequency data.

- **Aperiodicity** ⇒ the orbit map `ℝᵈ → Ω` is injective, so the flow has no compact orbits; combined with
  minimality this forces `Ω` to be a continuum with Cantor transversal.

- **Linear repetitivity (LR).** `T` is *linearly repetitive* if the repetitivity radius grows at most
  linearly: `R(r) ≤ C·r` for some `C > 0` and all `r ≥ 1` (i.e. every radius-`r` patch recurs within
  distance `Cr` of every point). LR is the strongest, most rigid form of order.
  - **Lagarias–Pleasants:** the hull of a linearly repetitive Delone set / tiling in `ℝⁿ` is **uniquely
    ergodic**, with fast (uniform) convergence to patch frequencies; LR is "the lowest possible aperiodic
    repetitivity." See *Linear repetitivity, I* (Lagarias–Pleasants / Damanik–Lenz),
    <https://arxiv.org/abs/math/0005062>, and the survey discussion in
    <https://arxiv.org/abs/2001.10725>.
  - **Primitive substitution tilings are linearly repetitive**, hence minimal + uniquely ergodic. This is
    why substitution systems are so well-behaved and why our tower lands inside the nicest class.

**Logical chain (substitution case):** primitive substitution ⇒ linearly repetitive ⇒ repetitive ⇒
minimal; and linearly repetitive ⇒ uniquely ergodic. Aperiodicity is a separate (generically satisfied)
condition that makes the dynamics non-trivial.

---

## 4. The hull as an INVERSE LIMIT — the Anderson–Putnam construction

**This is the section that is our tower.** Two results, in increasing specificity.

### 4.1 General FLC tilings: inverse limit of branched manifolds (Sadun–Williams)

> *"Let `Ω` be a space of tilings of `M`, with finite local complexity (relative to some symmetry group `Γ`)
> and closed in the natural topology. Then `Ω` is the inverse limit of a sequence of compact
> finite-dimensional branched manifolds."*
> — L. Sadun, *Tiling Spaces are Inverse Limits*, J. Math. Phys. 44 (2003) 5410–5414,
> <https://arxiv.org/abs/math/0210179> (general-`M` form; the `ℝᵈ` core is Sadun–Williams, *Ergodic Theory
> Dynam. Systems* 23 (2003)).

Concretely (survey, Thm 4.1):

> *"If `T` is a tiling with finite local complexity, then `X_T` is the inverse limit of a sequence of compact
> branched surfaces `K₁, K₂, …` and continuous maps `σₙ : Kₙ → Kₙ₋₁`."*

with the **inverse limit** defined the usual way:
```
⟵lim Kₙ  =  { (x₁, x₂, …) ∈ ∏ₙ Kₙ : σₙ(xₙ) = xₙ₋₁ for all n }.
```

The construction of the approximants is the load-bearing intuition:

> *"A point in `Kₙ` encodes a set of instructions for placing a tile containing the origin, a ring of tiles
> around it (the first corona), a second ring around that, … out to the `n`-th corona. The map
> `σₙ : Kₙ → Kₙ₋₁` simply forgets the outermost corona."*

So `Kₙ` is the **`n`-collared AP complex**: take the prototiles, attach to each a label recording its
`n`-corona (its neighborhood out to radius `n`), and glue two collared tiles along a face when their labels
are consistent there. Each `Kₙ` is a *branched manifold* (a CW-like space that is a manifold except on a
lower-dimensional "branch locus" where sheets merge — it locally looks like several `ℝᵈ`-charts glued along
shared faces, encoding the finitely many ways tiles meet). A point of the hull = a coherent choice of
"what's at the origin out to every scale," i.e. a thread through the tower. **`Ω` is the projective limit of
finite combinatorial data at every radius** — exactly "strict information at every rung assembling into a
non-trivial limit object."

### 4.2 Substitution tilings: a STATIONARY inverse limit of ONE complex (Anderson–Putnam)

For a tiling generated by a **substitution** (inflate-and-subdivide rule `ω`), the tower collapses to a
single space with a single self-map. This is the cleanest possible "tower."

- **Substitution / inflation.** Inflate `ℝᵈ` by a linear expansion `λ` (the **inflation factor**), then
  subdivide each expanded prototile into a patch of ordinary prototiles. Iterating builds larger and larger
  **supertiles**. The induced map on the hull, `ω : Ω → Ω` (inflate-and-subdivide), is a homeomorphism when
  the substitution is **recognizable / invertible** (each tiling has a *unique* decomposition into supertiles).

- **Anderson–Putnam theorem.** Let `Γ = Γ_AP` be the AP complex (one cell per prototile, faces glued by
  allowed adjacencies). The substitution induces a self-map `γ : Γ → Γ`. Then, **provided the substitution
  "forces the border,"**
  ```
  Ω  ≅  ⟵lim (Γ, γ)  =  { (x₀, x₁, x₂, …) ∈ Γ^ℕ : γ(xₙ₊₁) = xₙ } ,
  ```
  a *stationary* inverse limit (the same space `Γ` and the same bonding map `γ` at every rung) — one of
  R. F. Williams' **generalized solenoids**. The substitution `ω` on `Ω` is conjugate to the shift on the
  inverse limit.
  - Source: J. Anderson & I. Putnam, *Topological invariants for substitution tilings and their associated
    C\*-algebras*, Ergodic Theory Dynam. Systems **18** (1998) 509–537. Semantic Scholar:
    <https://www.semanticscholar.org/paper/Topological-invariants-for-substitution-tilings-and-Anderson-Putnam/1fbf0fe01b45349ad226444510af75769f469eb8>
  - Clean modern statement: Sadun, *Cohomology of Hierarchical Tilings*,
    <https://arxiv.org/abs/1406.0882>: *"If `σ` is a substitution that forces the border and has finite local
    complexity with respect to translations, then the corresponding tiling space `Ω` is homeomorphic to
    `Ω⁰` [the stationary inverse limit]."*

- **Forcing the border, and collaring.** A substitution **forces its border** if, for some `n`, the
  `n`-fold supertile of a tile determines the tiles immediately *outside* it (the pattern is forced across
  the seam). Not every substitution does this — but **collaring always fixes it**:

  > *"Rewriting a substitution in terms of collared tiles always yields a system that forces the border."*
  > — Sadun, <https://arxiv.org/abs/1406.0882>

  A **collared tile** is a prototile together with a label recording its nearest-neighbor pattern; one
  builds `Γ` from collared tiles (one copy of a prototile per admissible corona). With collaring, the
  AP theorem applies to *every* primitive FLC substitution. (This is the "one extra rung of bookkeeping"
  that makes the strict-extension survive — see §6.)

**Why this is exactly our object.** The inflation hierarchy is a tower; the hull is its stable inverse
limit; "the same complex and the same map at every level" is *stationarity*; recognizability is "the limit
is non-trivial / the threads are well-defined"; border-forcing-after-collaring is "after finitely much
bookkeeping the extension at each rung is clean enough to assemble." Our **T2 (stacking composition)** is the
statement that strictness composes up this tower; **F43 (continuum emergence)** is precisely the
inverse-limit existence statement.

---

## 5. Cohomology of tiling spaces and gap-labeling

### 5.1 Čech cohomology via the AP tower

Because `Ω` is an inverse limit of CW/branched complexes, its **Čech cohomology** is the corresponding
**direct (co)limit** — Čech cohomology turns inverse limits of spaces into direct limits of groups:
```
Ȟᵏ(Ω)  ≅  ⟶lim ( Ȟᵏ(Kₙ),  σₙ* )   (general FLC),
```
and for a substitution it is driven by the *single* induced map `γ*` on the cohomology of the one complex
`Γ`:
```
Ȟᵏ(Ω)  ≅  ⟶lim ( Ȟᵏ(Γ) --γ*--> Ȟᵏ(Γ) --γ*--> Ȟᵏ(Γ) --> ⋯ ).
```
- Source: Sadun, <https://arxiv.org/abs/1406.0882>; survey <https://arxiv.org/abs/math/0506054>:
  `Hᵏ(⟵lim Kₙ) = ⟶lim Hᵏ(Kₙ)`.
- Computationally: pick a basis for `Ȟ*(Γ)` (cellular), write `γ*` as an integer matrix, and the direct
  limit is the "eventual image / stable part" of that matrix raised to higher powers. **The substitution
  matrix on cohomology — and its Perron–Frobenius / Pisot eigenvalue structure — literally controls the
  invariant.** (See Gähler–Maloney–Rust, *Cohomology of Substitution Tiling Spaces*,
  <https://arxiv.org/abs/0811.2507>, and the 1-D treatments Barge–Diamond,
  <https://arxiv.org/abs/math/0702669>.)

### 5.2 Pattern-equivariant cohomology (Kellendonk–Putnam) — the concrete model

`Ȟ*(Ω)` is abstract; **pattern-equivariant (PE) cohomology** gives a hands-on cochain model living on
`ℝᵈ` itself:

> A (smooth or cellular) function/form `f` on `ℝᵈ` is **pattern-equivariant with radius `R`** if `f(x)`
> depends only on the tiling within distance `R` of `x`; equivalently, if `(T − x)` and `(T − y)` agree on
> the ball `B_R(0)` then `f(x) = f(y)`.
> — Kellendonk & Putnam (2003); see *Pattern-equivariant homology*,
> <https://msp.org/agt/2017/17-3/agt-v17-n3-p02-s.pdf>, and *Pattern-Equivariant Cohomology with Integer
> Coefficients* (Sadun), <https://arxiv.org/abs/math/0602066>.

Restricting the de Rham complex of `ℝᵈ` to PE forms (those determined by the local pattern out to some finite
radius) gives the **PE de Rham complex**, and

> **Theorem (Kellendonk–Putnam).** PE cohomology is isomorphic to the Čech cohomology of the tiling space,
> `H*_{PE}(T; ℝ) ≅ Ȟ*(Ω; ℝ)`. (Extended to `ℤ` and other coefficients by Sadun.)

This is the bridge between "topology of `Ω`" and "functions on the tiling you can actually write down." A PE
1-form is a locally-pattern-determined assignment of a number to each edge; closed-mod-exact such forms are
`H¹`. This is the natural home for our `∮_γ a` audit (§6).

### 5.3 What the cohomology measures: deformations and the image in `ℝᵈ`

`H¹(Ω; ℝᵈ)` is the **deformation space of the tiling**: it parametrizes how you can change the *shapes*
(edge/translation vectors) of tiles while keeping the combinatorics fixed.

- **Clark–Sadun deformation theory.** There is a natural map
  `I : {shape parameters} → H¹(Ω; ℝᵈ)` ("shape function" = vector-valued PE 1-cochain encoding edge
  displacements). Two tilings with the **same image under `I` are mutually locally derivable (MLD)**; when
  the difference of images is **asymptotically negligible**, the two systems are **topologically conjugate**
  (but not necessarily MLD). For substitutions there is a *simple eigenvalue test* (sign/expansion under
  `γ*`) for a class to be asymptotically negligible.
  - A. Clark & L. Sadun, *When shape matters: deformations of tiling spaces*, Ergodic Theory Dynam. Systems
    26 (2006): <https://sites.math.unt.edu/~alexc/shape9.pdf>; survey statement at
    <https://arxiv.org/abs/math/0506054> (Thm 5.1: "Deformations of `T` are parametrized by closed
    vector-valued 1-cochains on approximants to `X_T`; equal classes in `H¹(X_T, ℝᵈ)` ⇒ MLD").

- **Exact regularity (Sadun et al.).** The *top* cohomology controls patch frequencies quantitatively:
  > If `Ȟᵈ(Ω; ℚ) = ℚᵏ`, then there exist `k` patches whose appearance counts govern the appearance counts of
  > **every** other patch, giving uniform estimates on convergence of all patch frequencies to the ergodic
  > limit.
  > — *Exact Regularity and the Cohomology of Tiling Spaces*, <https://arxiv.org/abs/1004.2281>;
  > *Homological Pisot Substitutions and Exact Regularity*, <https://arxiv.org/abs/1001.2027>.

  This says the cohomology has a *direct, finite, measurable* readout — the rank `k` and the frequency
  module — which is precisely the kind of "topological number you can audit" we want.

### 5.4 Gap-labeling theorem and K-theory (Bellissard)

The spectral side. Put a self-adjoint **Schrödinger / Hamiltonian operator** `H` on `ℓ²` (or `L²`) modeling
a quasicrystal whose atomic positions follow the tiling. `H` is *affiliated* to the **C\*-algebra of the
hull**, the crossed product
```
A = C(Ω) ⋊ ℝᵈ      (continuous hull)        or       C(Ω₀) ⋊ ℤᵈ  /  groupoid C*-algebra (discrete hull).
```

- **Integrated density of states (IDS).** `N(E)` = number of eigenvalues of `H` per unit volume below
  energy `E`. `N` is constant on each **spectral gap**, so its value *labels* the gap.

- **Shubin's formula + K-theory.** If `E` lies in a gap, the spectral projection `P_E = χ_{(-∞,E]}(H)`
  belongs to `A`, and
  ```
  N(E) = τ(P_E),
  ```
  where `τ` is the canonical trace on `A` coming from the invariant measure `μ` (patch frequencies). Since
  `[P_E] ∈ K₀(A)`, the IDS value lands in the **image of the trace on K-theory**:
  ```
  N(E)  ∈  τ_*( K₀(A) )   ⊂  ℝ.
  ```
  — J. Bellissard, *K-theory of C\*-algebras in solid state physics* (gap-labeling origin); Bellissard,
  Bovier, Ghez, *Gap labelling theorems for one-dimensional discrete Schrödinger operators*; Bellissard,
  Herrmann, Zarrouati, *Hull of aperiodic solids and gap-labeling theorems*. Noncommutative-geometry
  overview: <https://arxiv.org/abs/cond-mat/9403065>. Telescopic/inverse-limit computation of the gap
  labels: *Spaces of Tilings, Finite Telescopic Approximations and Gap-Labeling*,
  <https://link.springer.com/article/10.1007/s00220-005-1445-z>.

- **The gap-labeling conjecture (now theorem).** The image of the trace on `K₀` equals the **frequency
  module** — the `ℤ`-module generated by the occurrence frequencies of finite patches:
  ```
  τ_*(K₀(C(Ω) ⋊ ℝᵈ))  =  ℤ-module generated by { freq(P) : P a patch }   =  μ_*(K₀(C(Ω))).
  ```
  > *"Given an invariant ergodic probability measure on the hull of a tiling, the integrated density of
  > states of any self-adjoint operator takes, on spectral gaps, values in the `ℤ`-module generated by the
  > occurrence probabilities of finite patches in the tiling."*

  This was the **Gap Labeling Conjecture of Bellissard**, proved independently around 2002–2003 by:
  - J. Kaminker & I. Putnam, *A proof of the Gap Labeling Conjecture* (via Connes' index theorem for
    foliated spaces), <https://arxiv.org/abs/math/0205102>;
  - M. Benameur & H. Oyono-Oyono; and
  - J. Bellissard, R. Benedetti & J.-M. Gambaudo.

- **Link to cohomology.** The trace on `K₀` factors through `Ȟ*(Ω)` paired against the invariant measure
  (Connes' pairing / the Ruelle–Sullivan current). So **gap labels are cohomology classes evaluated on the
  patch-frequency measure** — the spectral invariant and the topological invariant are the *same data* read
  two ways. (For substitutions, both reduce to the eigendata of the substitution matrix `γ*`.)

### 5.5 Pisot, diffraction, and the Perron eigenvalue (ties T1)

The inflation factor's arithmetic controls the spectrum:

- A substitution is of **Pisot type** if its Perron–Frobenius eigenvalue `λ` is a **Pisot number** (algebraic
  integer `> 1` whose Galois conjugates lie strictly inside the unit disk) and the remaining eigenvalues have
  modulus in `(0,1)`.
- **Pure-point diffraction ⟺ pure discrete dynamical spectrum.** The physical diffraction pattern of the
  tiling is pure point (Bragg peaks, "is a quasicrystal") **iff** the dynamical system `(Ω, ℝᵈ)` has pure
  discrete spectrum (eigenfunctions span `L²(Ω, μ)`).
- **Pisot Substitution Conjecture:** an irreducible Pisot-type substitution has pure discrete spectrum.
  Proved for `β`-substitutions (`β` a Pisot number). Sources: M. Barge, *Pure discrete spectrum in
  substitution tiling spaces*, <https://web.math.pmf.unizg.hr/~sonja/PDS-final.pdf>; Akiyama–Barge et al.,
  *On the Pisot Substitution Conjecture*; survey <https://arxiv.org/abs/2401.07771>.

This is exactly the **Pisot ↔ cut-and-project duality** named in our APPROACH.md: Pisot inflation factor ↔
pure-point diffraction ↔ model set. And the eigenvalue `λ` driving everything is the **Perron–Frobenius
eigenvalue of the substitution matrix** — the object T1 must certify.

---

## 6. Relevance to our shadow / strict-extension approach

This section connects the literature to the Six Birds monotile track (see `docs/APPROACH.md`,
`docs/CERTIFICATE.md`). The mapping is tight enough that several of our "to-build" pieces have an exact
external skeleton.

### 6.1 Hull-as-inverse-limit ⇒ F43 (continuum emergence) is the Anderson–Putnam theorem

Our F43 / "tiling hull as a stable inverse limit" is **literally** the Anderson–Putnam / Sadun–Williams
theorem of §4. We should adopt its vocabulary verbatim:

| Our framework | Tiling-space machinery |
|---|---|
| The inflation **tower** / ladder of rungs `j` | The inverse system `(Γ, γ)` (stationary) or `(Kₙ, σₙ)` |
| **Stable inverse limit** (the hull, F43) | `Ω = ⟵lim(Γ, γ)`, a Williams solenoid |
| "Same operator/complex at every rung" | **Stationarity** of the inverse limit |
| A point of the limit = a coherent thread | A tiling = compatible `(x₀, x₁, …)`, `γ(xₙ₊₁)=xₙ` |
| Non-trivial limit (limit is a continuum, not a point) | Recognizability ⇒ `ω` homeomorphism ⇒ `Ω` aperiodic continuum |
| "Finitely much bookkeeping cleans each rung" | **Collaring** ⇒ border-forcing ⇒ AP theorem applies |

The payoff: **F43 is not something we must prove from scratch.** It is a citable theorem (Anderson–Putnam
1998; Sadun–Williams 2003). Our novelty is not the existence of the inverse limit but the **strictness/
non-factorization carried along it** (below).

### 6.2 T2 (stacking-composition) lives on the tower's bonding maps

**T2 we must build:** *strict extension at rung `j` and at rung `j+1` ⟹ strict at `j → j+2`* — the
hierarchy survives every level of the inflation tower (home: F35 scale descent + F43).

The inverse-limit picture tells us precisely *what* "strict extension at rung `j`" should mean and *why*
composition is the natural operation:

- The tower's bonding map is `γ : Γ → Γ` ("apply the substitution / forget the outermost corona,"
  `σₙ : Kₙ → Kₙ₋₁`). Going up two rungs is `γ² = γ∘γ` — **composition of bonding maps is the substance of
  T2.** "Strict at `j` and `j+1` ⇒ strict at `j → j+2`" is the statement that the strictness witness is
  *closed under composing consecutive bonding maps*, i.e. it descends through `γ²`.

- **Border-forcing is exactly the mechanism that makes composition clean.** A substitution forces its border
  after `n` steps; once collared, *every* rung's extension determines the next rung's seam. The literature's
  "collar once, then border-forcing holds at all levels" is the prototype of "strict at two consecutive
  rungs ⇒ strict at the composite." Our T2 proof should be modeled on the **border-forcing / recognizability
  induction**: the unique-decomposition-into-supertiles property is preserved under `ω` (hence under `ω²`),
  which is the recognizability analogue of T2. References to mine for the induction:
  Anderson–Putnam (border forcing), Sadun *Cohomology of Hierarchical Tilings* (collaring lemma:
  <https://arxiv.org/abs/1406.0882>), and recognizability in *Introduction to hierarchical tiling dynamical
  systems* (<https://arxiv.org/abs/1802.09956>).

- **Non-trivial limit from strict-at-every-rung.** That strictness at every rung yields a *non-trivial*
  limit is the tiling-space fact that an aperiodic primitive substitution gives an inverse limit which is a
  non-degenerate continuum (the maps `γ*` on cohomology have an infinite, non-eventually-trivial direct
  limit). This is the "strict extension at every rung ⇒ non-trivial limit object" stacking-composition
  result our CERTIFICATE.md wants — and it has a concrete obstruction-theoretic form (the direct-limit
  cohomology is non-trivial).

**Concrete plan implied for T2:** phrase "strict extension at rung `j`" as a non-factorization of
`σⱼ : Kⱼ → Kⱼ₋₁` (a fiber-collision-with-split *living on the bonding map*, in the F8 sense — see §6.3),
then prove closure under composing `σ_{j+1} ∘ σⱼ` using the collaring/border-forcing induction. The home
F35 (scale descent / renormalization) is the substitution self-map `γ`; F43 supplies the limit.

### 6.3 Strict extension / non-factorization (F8) ⇒ the local-vs-hierarchical split

Our F8 certificate — *the hierarchical map `π₁` does not factor through the local-plane map `π₀`
⟺ two patches with `π₀` equal but `π₁` different* — is the tiling phenomenon **local indistinguishability +
globally forced hierarchy**. In tiling-space terms:

- `π₀` = the local-pattern map (which corona you sit in — a coordinate on `Γ` / the discrete hull).
- `π₁` = the supertile-membership map (which higher-level supertile you belong to — a coordinate one rung up
  the inverse limit).
- A **fiber-collision-with-split** = two tilings agreeing on a large ball (same `π₀`, same point of `Γ` at
  low level) but lying in *different supertiles* (different `π₁`, different threads of the inverse limit).
  This is precisely **non-injectivity of a single bonding map `σₙ`** together with the system staying
  separated upstairs — i.e. the inverse limit is *genuinely* a limit and not a quotient that collapses.

So F8-strictness is "the bonding maps `σₙ` are non-trivial covers / have splitting fibers," and T2 is "this
non-triviality composes up the tower." Both are statements about the same `(Γ, γ)` tower; the literature's
recognizability and border-forcing are the tools.

### 6.4 Cohomology / gap-labeling ⇒ T1 (spectral drive) and the eigenvalue/topological audit

Our **T1** (extend the cohomological audit `[a] ≠ 0 ∈ H¹ ⟺ ∮_γ a ≠ 0` to a **Perron-eigenvalue drive
certificate** for substitution matrices) maps cleanly onto established machinery:

- **The `∮_γ a` audit is the PE / Čech pairing.** A nonzero class in `H¹(Ω)` detected by a nonzero period
  integral is exactly the Kellendonk–Putnam PE-cohomology pairing (§5.2). Our cohomological audit is
  *already* the tiling-space invariant; we are on solid ground importing it.

- **The Perron eigenvalue is the right "drive."** Čech cohomology of a substitution hull is the **direct
  limit of `γ*`** (an integer matrix) — §5.1. Its growth/contraction is governed by the eigenvalues of the
  substitution matrix, whose top eigenvalue is the **Perron–Frobenius value `λ`** (= the inflation factor,
  Pisot in our setting). So "a Perron-eigenvalue drive certificate for substitution matrices" is
  well-posed: `λ` and its conjugates are precisely what decide which cohomology classes survive the direct
  limit (asymptotically negligible vs. not — Clark–Sadun, §5.3), and whether the spectrum is pure-point
  (Pisot conjecture, §5.5). T1's "trace-budget" shape (`A_X ⪯ B_n`, `tr(B_n)→0 ⟹ A_X=0`) is the **contracting
  Galois-conjugate** condition of a Pisot number: the sub-dominant eigenvalues `|λᵢ| < 1` are the vanishing
  trace budget; the surviving Perron direction is the non-trivial class.

- **The audit number is genuinely topological (gap-labeling).** Bellissard's gap-labeling (§5.4) certifies
  that the spectral/eigenvalue readout is a **topological invariant valued in `ℝ`** — `N(E) = τ_*[P_E]`, an
  element of the image of the trace on `K₀(C(Ω)⋊ℝᵈ)`, equal to the `ℤ`-module of patch frequencies. This is
  the rigorous version of "the eigenvalue data appears as a topological invariant with an image in `ℝ`,"
  and it is *finite/computable* for substitution tilings (telescopic approximation,
  <https://link.springer.com/article/10.1007/s00220-005-1445-z>). For our **no-overread / Lean-checkable
  audit**, gap-labeling + exact regularity (§5.3) say the load-bearing number is the trace of an explicit
  matrix's eventual image — a finite computation, matching CERTIFICATE.md field 6.

- **Galois-invariance of the inflation factor (CERTIFICATE field 4).** That `λ`'s trace, norm, and
  characteristic polynomial are rational while `λ` itself is an irrational Pisot number is *exactly* the
  Pisot-type substitution-matrix condition. The substitution matrix is an integer matrix; its char poly is
  in `ℤ[x]`; its Perron root is the irrational Pisot `λ`. The literature confirms this is the precise
  arithmetic that yields pure-point diffraction — our `√2`/`InvDesc`+`AggInv` profile is the Pisot/Galois
  profile.

### 6.5 Net assessment for the cascade

- **F43 / hull-as-inverse-limit: import, do not re-derive.** Anderson–Putnam (1998) + Sadun–Williams (2003)
  *are* the theorem. Cite them; instantiate our `(Z, f, Σ_f, E, 𝒜)` closure package as the AP tower
  `(Γ, γ)`.
- **T2 / stacking-composition: build, on a known skeleton.** Model the proof on the
  **collaring ⇒ border-forcing ⇒ recognizability** induction; phrase strictness as non-factorization of the
  bonding maps `σₙ` and prove closure under `σ_{j+1}∘σⱼ`. The non-trivial limit is the non-degeneracy of the
  direct-limit cohomology.
- **T1 / spectral drive: build, but the audit object already exists.** The `H¹` period-integral audit is the
  PE/Čech pairing; the "drive" is the Perron–Frobenius eigenvalue of the substitution matrix; the
  topological-ness of the eigenvalue readout is Bellissard gap-labeling; the finiteness/Galois-rationality is
  the Pisot substitution-matrix condition. Frame T1 as a *Pisot-Perron* certificate and the trace-budget is
  the contraction of the Galois conjugates.
- **SFT rarity argument:** orthogonal to this note (it is the Finite-Forcing/counting piece); but note that
  "almost no local rule forces a hierarchy" is consistent with "most candidate `(Γ, γ)` fail border-forcing
  / recognizability," which the AP framework makes checkable.

---

## 7. Authoritative sources (titles + URLs)

**Surveys / book (start here):**
- L. Sadun, *Topology of Tiling Spaces*, AMS Univ. Lecture Series 46 (2008): <https://books.google.com/books/about/Topology_of_Tiling_Spaces.html?id=dL8FCAAAQBAJ>
- L. Sadun, *Tilings, tiling spaces and topology*, Philosophical Magazine 86 (2006): <https://arxiv.org/abs/math/0506054>
- L. Sadun, *Cohomology of Hierarchical Tilings* (2014): <https://arxiv.org/abs/1406.0882>
- L. Sadun, *Introduction to hierarchical tiling dynamical systems* (2018): <https://arxiv.org/abs/1802.09956>

**Hull as inverse limit (Anderson–Putnam construction) — our tower:**
- J. Anderson & I. Putnam, *Topological invariants for substitution tilings and their associated C\*-algebras*, Ergodic Theory Dynam. Systems 18 (1998) 509–537: <https://www.semanticscholar.org/paper/Topological-invariants-for-substitution-tilings-and-Anderson-Putnam/1fbf0fe01b45349ad226444510af75769f469eb8>
- L. Sadun, *Tiling Spaces are Inverse Limits*, J. Math. Phys. 44 (2003) 5410–5414: <https://arxiv.org/abs/math/0210179> (and Sadun–Williams, ETDS 23 (2003), the `ℝᵈ` core).
- F. Gähler, G. Maloney, J. Rust, *Cohomology of Substitution Tiling Spaces*: <https://arxiv.org/abs/0811.2507>
- M. Barge, B. Diamond, *Cohomology in one-dimensional substitution tiling spaces*: <https://arxiv.org/abs/math/0702669>

**Cohomology, PE-cohomology, deformations:**
- J. Kellendonk & I. Putnam, *Pattern-equivariant functions and cohomology* (2003); J. Hunton et al., *Pattern-equivariant homology*: <https://msp.org/agt/2017/17-3/agt-v17-n3-p02-s.pdf>
- L. Sadun, *Pattern-Equivariant Cohomology with Integer Coefficients*: <https://arxiv.org/abs/math/0602066>
- A. Clark & L. Sadun, *When shape matters: deformations of tiling spaces*, ETDS 26 (2006): <https://sites.math.unt.edu/~alexc/shape9.pdf>
- M. Barge, B. Diamond, J. Hunton, L. Sadun, *Exact Regularity and the Cohomology of Tiling Spaces*: <https://arxiv.org/abs/1004.2281>; *Homological Pisot Substitutions and Exact Regularity*: <https://arxiv.org/abs/1001.2027>

**Gap-labeling / K-theory / spectrum (Bellissard):**
- J. Bellissard, A. Bovier, J.-M. Ghez, *Gap labelling theorems for one-dimensional discrete Schrödinger operators*; J. Bellissard, *Gap labelling theorems for Schrödinger operators*; *Noncommutative geometry of tilings and gap labelling*: <https://arxiv.org/abs/cond-mat/9403065>
- J. Bellissard, R. Benedetti, J.-M. Gambaudo, *Spaces of Tilings, Finite Telescopic Approximations and Gap-Labeling*, Comm. Math. Phys. (2006): <https://link.springer.com/article/10.1007/s00220-005-1445-z>
- J. Kaminker & I. Putnam, *A proof of the Gap Labeling Conjecture*: <https://arxiv.org/abs/math/0205102> (independently: Benameur–Oyono-Oyono; Bellissard–Benedetti–Gambaudo).

**Repetitivity / unique ergodicity / linear repetitivity:**
- J. Lagarias & P. Pleasants; D. Damanik & D. Lenz, *Linear repetitivity, I. Uniform subadditive ergodic theorems and applications*: <https://arxiv.org/abs/math/0005062>
- *Linear repetitivity beyond abelian groups*: <https://arxiv.org/abs/2001.10725>

**Pisot / diffraction (Pisot ↔ pure-point ↔ cut-and-project; ties T1 and APPROACH.md duality):**
- M. Barge, *Pure discrete spectrum in substitution tiling spaces*: <https://web.math.pmf.unizg.hr/~sonja/PDS-final.pdf>
- S. Akiyama, M. Barge, et al., *On the Pisot Substitution Conjecture*; survey *Pisot Substitution Conjecture and Rauzy Fractals*: <https://arxiv.org/abs/2401.07771>
