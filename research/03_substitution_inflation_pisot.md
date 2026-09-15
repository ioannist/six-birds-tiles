# Substitution / Inflation Tilings and Their Algebra (Perron–Frobenius, Pisot/Salem)

Research note 03. Compiled 2026-06-09 from primary sources (arXiv, Annals, Tilings
Encyclopedia / Bielefeld, MathWorld, Wikipedia). All quotations are attributed inline
with URLs. This note feeds the "eigenvalue audit" and "non-factorization certificate"
parts of the shadow / strict-extension monotile program.

---

## 1. Overview

A **substitution (inflation) tiling** is built by a single local rule applied at every
scale: take each prototile, blow it up by a fixed linear factor (the **inflation factor**
λ), and cut the blown-up tile into a fixed pattern of original-size prototiles. Iterating
this rule generates larger and larger **supertiles**; the limit (hull) is a tiling space
with a hierarchical, self-similar structure that is typically **aperiodic** yet **highly
ordered**.

Three algebraic facts make this a rigorous machine rather than a picture:

1. **The combinatorics linearize.** Forgetting geometry and counting "how many tiles of
   type *j* appear in the inflation of tile *i*" gives the **substitution (abelianization)
   matrix** *M*. By Perron–Frobenius, a *primitive* *M* has a unique dominant eigenvalue
   λ_PF, which is the **volume** inflation factor; in *d* dimensions λ_PF = λ^d for the
   *linear* factor λ. This is the **eigenvalue audit**.

2. **The inflation factor is constrained.** Not every number can be an inflation factor.
   λ must be a **Perron number** (Lind, 1D; Thurston/Kenyon, the plane). When the tiling is
   "quasicrystalline" (a model set / pure-point diffractive), λ is forced to be **Pisot**
   (or Salem). This is the **algebra of inflation factors**.

3. **The hierarchy is forced and rigid.** A primitive *aperiodic* substitution is
   **recognizable** (Mossé) and has the **unique composition property** (Solomyak): every
   tiling in the hull can be *uniquely* de-substituted — there is exactly one way to group
   tiles back into supertiles. Locally the tiling looks ambiguous, but globally the
   hierarchy is determined. This is precisely a **non-factorization / unique-decomposition
   certificate**, and (Mozes, Goodman-Strauss) it is what lets a substitution be enforced
   by *finite local matching rules*.

The note ends (§8) by mapping each of these onto the project's shadow / strict-extension
approach.

---

## 2. Precise definitions

### 2.1 Tile substitution and the inflation factor λ

Following N. P. Frank, *A primer on substitution tilings of the Euclidean plane*
(arXiv:0705.1142, https://arxiv.org/abs/0705.1142): a **tile substitution** with
expansion λ on a finite **prototile set** {*t₁,…,t_m*} is a rule that (i) inflates each
prototile *tᵢ* by the linear map (scaling by λ), and (ii) subdivides the inflated tile
λ·*tᵢ* into a patch of translated/rotated copies of the prototiles. λ is the **inflation
factor** (also expansion or stretching factor).

The Tilings Encyclopedia glossary defines it concisely: the inflation factor is "the
linear map that gives the scaling for a substitution rule, before the replacement by new
tiles"; in the plane this is "multiplication by a complex number"
(https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/).

A tiling **T** is **self-similar** (resp. **self-affine**) if applying the inflation map
and subdividing reproduces **T** itself; the hull is the orbit closure of **T** under
translations.

### 2.2 The substitution (abelianization / incidence) matrix M

Define the *m × m* nonnegative integer matrix *M* (a.k.a. **substitution, abelianization,
transition, incidence, composition,** or **subdivision** matrix) by

> *M_{ij}* = number of copies of prototile *tᵢ* contained in the subdivision of the
> inflated prototile λ·*t_j*.

(Index conventions differ by author; *M* or *Mᵀ* — what matters is the spectrum.)
Iterating, *Mⁿ* counts prototiles in the *n*-th level supertile. The Bielefeld glossary
notes the abelianization "forgets the order of letters," letting linear algebra govern the
self-similar growth (https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/).

**1-D symbolic example (Fibonacci).** Substitution *a → ab*, *b → a*. Matrix
*M* = [[1,1],[1,0]] (the Fibonacci matrix). Characteristic polynomial *x² − x − 1*;
eigenvalues φ = (1+√5)/2 and 1−φ = −1/φ. The dominant eigenvalue is the golden ratio φ;
consecutive Fibonacci ratios → φ.

### 2.3 Primitivity

*M* (equivalently the substitution) is **primitive** if some power *Mⁿ* has *all* entries
strictly positive — i.e. for some *n*, every prototile appears in the *n*-th inflation of
every prototile. Primitivity is the hypothesis that unlocks Perron–Frobenius and forces
**minimality** and uniform tile frequencies on the hull.

### 2.4 Perron–Frobenius ⇒ inflation factor (the eigenvalue audit)

Perron–Frobenius theorem (for primitive nonnegative *M*): *M* has a real eigenvalue
λ_PF > 0 that is **simple**, **strictly dominant** (|μ| < λ_PF for all other eigenvalues
μ), with strictly positive left and right eigenvectors.

The Bielefeld/Berthé survey states it directly: "if the substitution matrix is primitive,
then it admits a strictly dominant eigenvalue that is positive, and this eigenvalue is
called the inflation factor, or expansion factor of the substitution"
(Berthé–Yassawi et al., *Meyer sets, Pisot numbers, and self-similarity in symbolic
dynamical systems*, arXiv:2404.04116, https://arxiv.org/abs/2404.04116).

**Dimensional bookkeeping (important):** λ_PF counts *tiles*, hence scales like **volume**.
For a self-similar tiling of ℝ^d with *linear* factor λ,

> **λ_PF = λ^d.**

In 1-D (symbolic) the PF eigenvalue *is* the geometric length-scaling λ. In the plane
(d = 2) the PF eigenvalue equals λ² (area scaling). Eigenvector data also has meaning: the
**right** PF eigenvector gives relative tile **frequencies**; the **left** PF eigenvector
gives relative tile **volumes/areas**. (Confirmed across sources, e.g.
arXiv:1004.2281 "Exact Regularity and the Cohomology of Tiling Spaces,"
https://arxiv.org/abs/1004.2281; and Solomyak, *Tilings and Dynamics*,
https://u.math.biu.ac.il/~solomyb/RESEARCH/notes6.pdf.)

### 2.5 Canonical examples

| Tiling | dim | prototiles | linear λ | λ_PF (= λ^d) | algebra of λ |
|---|---|---|---|---|---|
| **Fibonacci** (symbolic) | 1 | 2 letters (a,b) | φ = (1+√5)/2 ≈ 1.618 | φ | Pisot (golden ratio), unit |
| **Penrose** (rhombs / Robinson triangles) | 2 | 2 rhombs (or 4 triangles) | φ | φ² = φ+1 ≈ 2.618 | golden ratio, Pisot, unit |
| **Ammann–Beenker** | 2 | square + 45° rhomb | 1+√2 (silver mean) | (1+√2)² = 3+2√2 | silver ratio, Pisot, unit |
| **chair** | 2 | 4 L-shapes (square reptile) | 2 | 4 | rational integer (degenerate Pisot) |
| **table / domino** | 2 | rectangles (dominoes) | 2 | 4 | rational integer |
| **half-hex** | 2 | 6 half-hexagons (rotations) | 2 | 4 | rational integer |

Notes and sources:
- **Penrose:** scale factor λ = φ; Perron–Frobenius eigenvalue Λ_PF = φ²
  (Wikipedia "Penrose tiling"; goldenratio.wikidot Penrose page,
  http://goldenratio.wikidot.com/penrose-tiling). Robinson-triangle decomposition uses the
  Fibonacci matrix [[1,1],[1,0]] with eigenvalues φ, −1/φ.
- **Ammann–Beenker:** "The substitution factor is 1+√2 — sometimes called the 'silver
  mean' — … the first irrational inflation factor known which is not related to the golden
  mean" (Tilings Encyclopedia,
  https://tilings.math.uni-bielefeld.de/substitution/ammann-beenker/). The 1-D "Conway
  worm" substitution *R → RrR, r → R* (Pell substitution) has matrix [[2,1],[1,0]] with
  eigenvalues 1+√2 and 1−√2 (Wikipedia "Ammann–Beenker tiling",
  https://en.wikipedia.org/wiki/Ammann%E2%80%93Beenker_tiling).
- **chair / table / half-hex:** all are **self-similar Pisot substitution tiling spaces
  with λ = 2**. The chair has four (square) prototiles; the half-hex has six prototiles
  (a half-hexagon and its π/3 rotations). Baake–Gähler–Grimm, *Hexagonal Inflation Tilings
  and Planar Monotiles* (Symmetry 4 (2012) 581; https://www.mdpi.com/2073-8994/4/4/581;
  preprint https://oro.open.ac.uk/34803/) clarify the half-hex/monotile relation and show
  these hulls have a **model-set** structure with aperiodic local rules. Note λ = 2 is a
  (degenerate) Pisot number, but it is **not a unit** — relevant below for diffraction.
- **Padovan/Perrin** (1-D): substitution *0 → 1, 1 → 2, 2 → 01* (or variants) has inflation
  factor the **plastic number** ρ ≈ 1.3247, root of *x³ − x − 1*; this is the **smallest
  Pisot number** (see §3).

---

## 3. The algebra of inflation factors: Perron, Pisot, Salem

### 3.1 Number classes (definitions)

- **Perron number:** a real algebraic integer λ > 1 all of whose Galois conjugates are
  **strictly smaller than λ in modulus**. (Bielefeld: "an algebraic integer which is
  strictly larger than its algebraic conjugates in modulus,"
  https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/.)
- **Complex Perron number:** an algebraic integer λ with |λ| > 1 such that every Galois
  conjugate *except its own complex conjugate* has strictly smaller modulus (Kenyon–
  Solomyak, *On the characterization of expansion maps for self-affine tilings*,
  arXiv:0801.1993, https://arxiv.org/abs/0801.1993).
- **Pisot (PV) number:** a real algebraic integer β > 1 all of whose **other conjugates
  have modulus < 1**. (Berthé et al., arXiv:2404.04116: "A real algebraic integer β > 1 is
  a Pisot number if all of its other algebraic conjugates λ satisfy |λ| < 1.")
- **Salem number:** a real algebraic integer β > 1 with **at least one conjugate of modulus
  exactly 1**, all others of modulus ≤ 1. (Same source: "… if at least one of its algebraic
  conjugates λ satisfies |λ| = 1 while its other conjugates have modulus smaller than 1.")

Containments: **Pisot ⊂ Perron**, and **Salem ⊄ Perron** (a Salem number has conjugates
*equal* to it in modulus, so it is *not* Perron). Every Pisot number is Perron; the converse
fails.

### 3.2 Which numbers are inflation factors? (Lind, Thurston, Kenyon)

This is the structural constraint — the "audit passes only for Perron numbers."

- **Lind (1984), 1-D / self-similar line.** "There is a self-similar tiling of the line ℝ
  with expansion λ if and only if |λ| is a Perron number" — i.e. an expansion factor for a
  self-similar tiling of the line **must be a Perron number**, and **every** Perron number
  arises this way (Kenyon–Solomyak summary, arXiv:0801.1993; Solomyak *Tilings and
  Dynamics*, https://u.math.biu.ac.il/~solomyb/RESEARCH/notes6.pdf). This is exactly the
  Perron–Frobenius eigenvalue of a primitive nonnegative integer matrix.
- **Thurston (1989, AMS Colloquium Lectures *Groups, Tilings and Finite State Automata*).**
  For self-affine tilings of the plane: the expansion factor λ (acting as *z ↦ λz*) **must
  be a complex Perron number**. The Bielefeld glossary states: "each inflation factor q of a
  volume hierarchic tiling is a Perron number"
  (https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/).
- **Kenyon (converse).** "For each complex Perron number there is a volume hierarchic
  tiling" (Bielefeld glossary, *ibid.*); see also Kenyon, *The construction of self-similar
  tilings*, GAFA 6 (1996), https://link.springer.com/article/10.1007/BF02249260. Together
  with Thurston this gives **necessary and sufficient**: λ is a planar self-affine expansion
  factor **iff** λ is a complex Perron number (Kenyon–Solomyak, arXiv:0801.1993).

So: **inflation factors = (complex) Perron numbers.** Perron is the *general* constraint;
Pisot/Salem is the *finer* constraint that appears once we demand quasicrystalline
(model-set / pure-point) order.

### 3.3 Meyer's theorem: Pisot/Salem from the self-similar Meyer condition

The bridge from "ordered point set + self-similarity" to Pisot/Salem:

> **Meyer's theorem** (Berthé et al., arXiv:2404.04116, Thm 2.2): "If Λ is a Meyer set,
> β > 1 is a real number and if βΛ ⊂ Λ, then β is either a Pisot number or a Salem number.
> Conversely, for each dimension *n* and for each Pisot or Salem number β, there exists a
> model set Λ ⊂ ℝⁿ such that βΛ ⊂ Λ."
> (https://arxiv.org/abs/2404.04116)

So as soon as a self-similar structure is a **Meyer set** (uniformly discrete, relatively
dense, with Λ − Λ uniformly discrete — the natural "quasicrystal" hypothesis) and the
inflation maps it into itself, the inflation factor is **forced to be Pisot or Salem**, not
merely Perron. The Bielefeld model-set glossary records the consequence: "If V is a model
set and the substitution factor λ satisfies λV ⊆ V, then λ must be a PV number"
(https://tilings.math.uni-bielefeld.de/glossary/model-set/).

### 3.4 Named examples (golden, silver, plastic; the Salem floor)

- **Golden ratio** φ = (1+√5)/2, root of *x² − x − 1*. Pisot, an algebraic **unit**
  (constant term ±1). Inflation factor of Fibonacci and (as φ or φ²) Penrose. φ is also the
  **smallest limit point** of the set of Pisot numbers (Dufresnoy–Pisot).
- **Silver ratio / silver mean** 1+√2 ≈ 2.414, root of *x² − 2x − 1*. Pisot, unit.
  Inflation factor of Ammann–Beenker; "the first irrational inflation factor … not related
  to the golden mean" (Bielefeld, *ibid.*).
- **Plastic number** ρ ≈ 1.32472, root of *x³ − x − 1*. This is the **smallest Pisot
  number** (MathWorld "Plastic Constant,"
  https://mathworld.wolfram.com/PlasticConstant.html; Bielefeld
  https://tilings.math.uni-bielefeld.de/glossary/plastic_number/). It is a unit (constant
  term −1) and the inflation factor of the Padovan/Perrin substitution. Its defining feature
  for us is its **smallness** — it is the floor of the Pisot set, so the slowest-inflating
  Pisot hierarchy possible.
- **Salem floor (Lehmer's number)** ≈ 1.17628, the largest root of Lehmer's polynomial
  *x¹⁰ + x⁹ − x⁷ − x⁶ − x⁵ − x⁴ − x³ + x + 1*; the **smallest known Salem number** and the
  smallest known Mahler measure > 1 of a noncyclotomic integer polynomial — whether it is
  the true minimum is **Lehmer's open problem** (Wikipedia "Salem number",
  https://en.wikipedia.org/wiki/Salem_number).

**Takeaway for the audit:** *Perron* is the gate any inflation factor must pass; *Pisot*
(and ideally a *unit*) is the gate for clean quasicrystalline diffraction; *Salem* sits on
the boundary and is exactly the subtle case the Pisot conjecture excludes.

---

## 4. The Pisot substitution conjecture

### 4.1 Statement

Diffraction/dynamics dictionary: for a primitive substitution tiling, the **diffraction
spectrum is pure point (Bragg peaks only) iff the tiling dynamical system has pure discrete
(pure point) dynamical spectrum**. The conjecture predicts when this happens.

> **Pisot Substitution Conjecture (irreducible form).** A one-dimensional primitive
> substitution whose inflation factor λ is a **Pisot** number and whose substitution matrix
> has an **irreducible** characteristic polynomial (equivalently: deg(λ) = size of the
> matrix, the "irreducible Pisot" case) has **pure discrete spectrum** (equivalently, the
> associated point sets are **regular model sets** and diffraction is pure point).

Sources: Akiyama et al., *Open Problems and Conjectures related to the Theory of
Mathematical Quasicrystals* (arXiv:1604.06280, https://arxiv.org/abs/1604.06280); EMS
survey *The Pisot Conjecture — From Substitution Dynamical Systems to …*
(https://ems.press/content/serial-article-files/46214). The **geometric / tiling form**
(Bielefeld): the **PV-conjecture** "asks whether every primitive substitution tiling whose
inflation factor is an irrational PV number is mld [mutually locally derivable] to a model
set (possibly under further conditions)"
(https://tilings.math.uni-bielefeld.de/glossary/model-set/).

What it relates: **Pisot inflation ⇄ pure-point diffraction ⇄ model-set (cut-and-project)
structure**. The Salem case and the "reducible" Pisot case are deliberately outside the
clean statement (they can fail or are subtler).

### 4.2 Current status (open in general; many partial results)

- **Two letters: PROVED.** Every Pisot substitution on a two-letter alphabet has pure
  discrete spectrum — **Hollander–Solomyak (2003)** via the balanced-pair algorithm,
  combined with **Barge–Diamond**'s proof of the strong coincidence conjecture for two
  letters (Cambridge ETDS, *Two-symbol Pisot substitutions have pure discrete spectrum*,
  https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/abs/twosymbol-pisot-substitutions-have-pure-discrete-spectrum/602A997C102D38DB5F9C3B84B6CACB59).
- **β-substitutions: PROVED.** Barge (and Barge–Štimac–Williams) established the conjecture
  for β-substitutions / numeration-system substitutions (*The Pisot conjecture for
  β-substitutions*, Cambridge ETDS; arXiv:1505.04408,
  https://arxiv.org/abs/1505.04408).
- **Three letters, restricted: PROVED by exhaustive search.** Akiyama–Gähler–Lee verified
  the conjecture for all three-letter substitutions whose incidence matrix has trace ≤ 2.
- **General case (≥ 3 letters / higher dimensions): OPEN.** No counterexample is known
  despite extensive computer search, and no general proof exists (Akiyama et al.,
  arXiv:1604.06280). Reformulations continue (overlap/strong coincidence, prefix–suffix
  automata, the Coincidence Rank Conjecture; e.g. arXiv:2401.07771 *Pisot Substitution
  Conjecture and Rauzy Fractals*).

---

## 5. Recognizability / unique composition (the non-factorization certificate)

This is the load-bearing section for the project: a primitive aperiodic substitution
admits a **unique** de-substitution, even though *no bounded patch alone* reveals the
hierarchy. Local indistinguishability, globally forced hierarchy.

### 5.1 Recognizability (Mossé) — the symbolic statement

A substitution σ is **recognizable** if there is a finite "window" radius ℓ such that the
local pattern within ℓ of a point determines whether that point is a **cutting point**
(supertile boundary) of σ — and hence determines the unique de-substitution.

> **Definition (Mossé recognizability)** (Berthé et al., *Recognizability for sequences of
> morphisms*, arXiv:1705.00167, Def. 2.4, https://arxiv.org/abs/1705.00167): σ : 𝒜 → ℬ⁺ is
> recognizable for *x* if there is ℓ such that for cutting points *m*, whenever
> *y*[*m*−ℓ, *m*+ℓ) = *y*[*m′*−ℓ, *m′*+ℓ) then *m′* is also a cutting point.

> **Theorem (Mossé 1992, 1996).** "Every aperiodic primitive substitution σ is recognizable
> in the shift X(σ)" (bilaterally recognizable). (arXiv:1705.00167; see also Akiyama–Tan,
> *On B. Mossé's unilateral recognizability theorem*, arXiv:1801.03536,
> https://arxiv.org/abs/1801.03536.)

The window ℓ is finite but can be larger than any single supertile: that is the precise
sense in which the hierarchy is **not locally visible** yet **globally unique**.

### 5.2 Unique composition property (Solomyak) — the geometric statement

For self-affine tilings the same phenomenon is called the **unique composition property**
(UCP), a.k.a. **composition–decomposition** or **recognizability**:

> **Unique composition property.** Every tiling **T** in the hull admits **exactly one**
> partition of its tiles into level-1 supertiles consistent with the inflation; i.e. the
> de-substitution map is well defined and injective on the hull.

> **Solomyak's recognizability theorem.** For a primitive self-affine tiling, **the unique
> composition property holds if and only if the tiling is non-periodic (aperiodic)**.
> (B. Solomyak, *Dynamics of self-similar tilings*, Ergodic Theory Dynam. Systems 17
> (1997), and *Tilings and Dynamics* lecture notes,
> https://u.math.biu.ac.il/~solomyb/RESEARCH/notes6.pdf. The Frank primer
> (arXiv:0705.1142) and Anderson–Putnam both adopt UCP as the standing hypothesis.)

Equivalence in one line: **(primitive) aperiodicity ⇔ unique de-substitution ⇔
recognizability**. Aperiodicity is not an obstruction to structure — it is *exactly the
condition that makes the hierarchy rigid and the factorization unique*.

### 5.3 Why this is a "non-factorization certificate" + matching rules

Recognizability is what converts a substitution into **enforceable local rules**:

- **Mozes (1989).** *Tilings, substitution systems and dynamical systems generated by them*
  — proved that a large class of substitution systems (with the unique composition /
  recognizability property) in dimension ≥ 2 can be enforced by **finite local matching
  rules** (are sofic).
- **Goodman-Strauss (1998).** *Matching rules and substitution tilings*, Annals of
  Mathematics 147(1), 181–223 (https://annals.math.princeton.edu/articles/12903): "for any
  substitution tiling in ℝ^d (d > 1), subject to relatively mild conditions, one can
  construct local rules that force the … global structure." This **generalizes Mozes** and
  "covers all known examples of hierarchical aperiodic tilings." (Recognizability is the
  key hypothesis enabling the construction; see Tilings Encyclopedia "Matching Rules,"
  https://tilings.math.uni-bielefeld.de/glossary/matching-rules/.)

Interpretation for us: recognizability says the **only** way a local patch can be completed
to an admissible tiling is the substitution way — there is **no alternative (periodic or
rival-hierarchical) factorization** of the tiling space. That non-existence of a competing
de-substitution is the certificate the strict-extension argument relies on.

---

## 6. Substitution ⇄ cut-and-project (model set) duality

Two charts of the same object: a substitution tiling can often **also** be described as a
**cut-and-project (model) set** — a slice of a higher-dimensional lattice projected through
a window. This is the "two coordinate systems" picture.

### 6.1 Definitions

- **Cut-and-project scheme:** a triple (ℝ^d "physical" × ℝ^k "internal"  ⊃  lattice *L*),
  with projections π (to physical) and π_int (to internal). A **model set** Λ = { π(x) :
  x ∈ *L*, π_int(x) ∈ *W* } for a **window** *W* with nonempty interior and compact closure
  (Bielefeld "Model Set," https://tilings.math.uni-bielefeld.de/glossary/model-set/;
  "Cut and Project," https://tilings.math.uni-bielefeld.de/glossary/cut-and-project/).
- **Hof–Schlottmann:** "each model set is pure point diffractive" (Bielefeld "Model Set").
- **Model set ⊂ Meyer set** (always), but not conversely.

### 6.2 When is a substitution tiling a model set, and vice versa

- **Forward (de Bruijn → general).** de Bruijn first showed the Penrose rhomb tiling is a
  projection (cut-and-project) set; this grew into the algebraic theory of model sets
  (reformulating Meyer's work). Penrose and Ammann–Beenker are model sets (Bielefeld,
  "Model Set").
- **Spectral criterion.** Under mild conditions, **a primitive substitution tiling has pure
  discrete spectrum ⇔ its point sets are regular model sets** in a cut-and-project scheme
  (Lee–Akiyama–… , *Pure discrete spectrum and regular model sets in d-dimensional unimodular
  substitution tilings*, Acta Cryst. A; PMC https://pmc.ncbi.nlm.nih.gov/articles/PMC7478237/;
  arXiv mirror via IUCr https://onlinelibrary.wiley.com/iucr/doi/10.1107/S2053273320009717).
  This is exactly the content the Pisot conjecture is trying to pin down.
- **The internal space is set by the Galois conjugates of λ.** When λ is an **irrational
  Pisot unit**, the internal (perp) space is **Euclidean** and built from the *conjugate*
  embeddings of the algebraic field ℚ(λ); the window is (a closure of) the **Rauzy fractal**
  / atomic surface. Bielefeld: if λ "is an irrational PV number … the tiling is a cut and
  project tiling," and "if the factor is also an algebraic unit, then the internal space
  will be Euclidean" (https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/). The
  Fourier transform of the Rauzy fractal yields the Bragg amplitudes (Baake–Gähler–Grimm,
  *Fourier transform of Rauzy fractals and point spectrum of 1D Pisot inflation tilings*,
  arXiv:1907.11012, https://arxiv.org/abs/1907.11012).

### 6.3 Star-duality / Galois-duality (Thurston → Frettlöh)

The two charts are linked by a **duality**:

- **Thurston's Galois duality:** in the Pisot-unit case, the inflation acts as λ in physical
  space and as its **Galois conjugate(s)** (modulus < 1) in internal space; the window
  (Rauzy fractal) is the attractor of the *dual* (contractive) iterated function system
  driven by those conjugates.
- **Frettlöh (2008), *Duality of Model Sets Generated by Substitutions*** (arXiv:math/0601064,
  https://arxiv.org/abs/math/0601064): develops a **star-duality** principle (noted earlier
  by Gelbrich for IFS) and uses it to **prove rigorously that a given substitution tiling
  arises from a model set**, constructing the dual Rauzy fractals explicitly. Frettlöh–Sing,
  *Self-dual tilings with respect to star-duality* (arXiv:0704.2528,
  https://arxiv.org/abs/0704.2528) generalize "Thurston's concept of Galois-duality to
  arbitrary cut-and-project sets," depending on the **star map** rather than Galois conjugacy
  per se. Cut-and-project schemes for the general Pisot-family case: Lee–… ,
  *Cut-and-Project Schemes for Pisot Family Substitution Tilings*
  (https://www.researchgate.net/publication/328326654).

**Summary of the duality:** substitution = "physical/expanding" description; model set =
"internal/contracting (window)" description. The change of charts is the Galois/star map;
the inflation factor's conjugates are the internal expansion data; existence of the dual
(a genuine window with interior) is *equivalent* to pure-point diffraction, i.e. to the
Pisot/model-set property.

---

## 7. Authoritative sources (titles + URLs)

Primary / survey:
- N. P. Frank, *A primer on substitution tilings of the Euclidean plane* — arXiv:0705.1142,
  https://arxiv.org/abs/0705.1142
- V. Berthé, R. Yassawi, et al., *Meyer sets, Pisot numbers, and self-similarity in symbolic
  dynamical systems* — arXiv:2404.04116, https://arxiv.org/abs/2404.04116
  (HTML: https://arxiv.org/html/2404.04116v1)
- B. Solomyak, *Tilings and Dynamics* (lecture notes) —
  https://u.math.biu.ac.il/~solomyb/RESEARCH/notes6.pdf
- B. Solomyak, *Dynamics of self-similar tilings*, Ergodic Theory Dynam. Systems 17 (1997)
  (unique composition property; weak-mixing ⇔ non-Pisot expansion).

Inflation-factor algebra (Perron/Pisot/Salem):
- D. Lind (1984), self-similar tilings of the line ⇔ Perron numbers (via Kenyon–Solomyak
  arXiv:0801.1993, https://arxiv.org/abs/0801.1993).
- W. Thurston, *Groups, Tilings and Finite State Automata*, AMS Colloquium Lectures, 1989
  (complex Perron numbers as planar expansion factors).
- R. Kenyon, *The construction of self-similar tilings*, GAFA 6 (1996) —
  https://link.springer.com/article/10.1007/BF02249260
- R. Kenyon, B. Solomyak, *On the characterization of expansion maps for self-affine
  tilings* — arXiv:0801.1993, https://arxiv.org/abs/0801.1993
- Tilings Encyclopedia (Bielefeld), *Inflation Factor* —
  https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/
- MathWorld, *Plastic Constant* (smallest Pisot) —
  https://mathworld.wolfram.com/PlasticConstant.html ;
  Bielefeld *Plastic Number* — https://tilings.math.uni-bielefeld.de/glossary/plastic_number/
- Wikipedia, *Salem number* (Lehmer's number, smallest known Salem) —
  https://en.wikipedia.org/wiki/Salem_number

Pisot substitution conjecture:
- S. Akiyama, M. Barge, V. Berthé, J.-Y. Lee, A. Siegel, *Open Problems and Conjectures
  related to the Theory of Mathematical Quasicrystals* — arXiv:1604.06280,
  https://arxiv.org/abs/1604.06280
- M. Barge, *The Pisot Conjecture — From Substitution Dynamical Systems to …* (EMS survey) —
  https://ems.press/content/serial-article-files/46214
- M. Hollander, B. Solomyak, *Two-symbol Pisot substitutions have pure discrete spectrum*,
  ETDS (2003) —
  https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/abs/twosymbol-pisot-substitutions-have-pure-discrete-spectrum/602A997C102D38DB5F9C3B84B6CACB59
- *The Pisot conjecture for β-substitutions*, ETDS — arXiv:1505.04408,
  https://arxiv.org/abs/1505.04408

Recognizability / matching rules:
- B. Mossé (1992, 1996); Berthé et al., *Recognizability for sequences of morphisms* —
  arXiv:1705.00167, https://arxiv.org/abs/1705.00167 ; Akiyama–Tan,
  *On B. Mossé's unilateral recognizability theorem* — arXiv:1801.03536,
  https://arxiv.org/abs/1801.03536
- S. Mozes, *Tilings, substitution systems and dynamical systems generated by them*,
  J. Analyse Math. 53 (1989).
- C. Goodman-Strauss, *Matching rules and substitution tilings*, Annals of Math. 147 (1998)
  181–223 — https://annals.math.princeton.edu/articles/12903

Substitution ⇄ model-set duality:
- D. Frettlöh, *Duality of Model Sets Generated by Substitutions* — arXiv:math/0601064,
  https://arxiv.org/abs/math/0601064
- D. Frettlöh, B. Sing, *Self-dual tilings with respect to star-duality* — arXiv:0704.2528,
  https://arxiv.org/abs/0704.2528
- J.-Y. Lee et al., *Pure discrete spectrum and regular model sets in d-dimensional
  unimodular substitution tilings*, Acta Cryst. A —
  https://pmc.ncbi.nlm.nih.gov/articles/PMC7478237/
- Baake–Gähler–Grimm, *Hexagonal Inflation Tilings and Planar Monotiles*, Symmetry 4 (2012)
  581 — https://www.mdpi.com/2073-8994/4/4/581 (chair / half-hex, λ = 2, model sets)
- Baake–Gähler–Grimm, *Fourier transform of Rauzy fractals and point spectrum of 1D Pisot
  inflation tilings* — arXiv:1907.11012, https://arxiv.org/abs/1907.11012
- General reference: M. Baake, U. Grimm, *Aperiodic Order, Vol. 1: A Mathematical
  Invitation*, Cambridge Univ. Press (2013) — the standard text covering all of the above.

---

## 8. Relevance to our shadow / strict-extension approach

We are designing a **higher-layer hierarchy** and **projecting down** to discover a new
aperiodic monotile. The three pillars above map onto our method exactly:

### (a) Perron eigenvalue ⇒ our eigenvalue audit
The inflation factor λ we choose for the higher layer is **not free**: by Lind / Thurston /
Kenyon it must be a **(complex) Perron number**, and the value that we can actually *measure*
from the layer combinatorics is the **Perron–Frobenius eigenvalue of the substitution matrix
M**, which equals **λ^d** (volume scaling; area scaling λ² in the plane). Concretely the
audit is:
1. Write down *M* from the proposed layer subdivision; check **primitivity** (some *Mⁿ* > 0)
   — without it there is no single dominant λ and the construction is ill-posed.
2. Compute λ_PF and take the *d*-th root to get the **linear λ**; verify λ is **Perron**
   (else no self-affine tiling exists — hard stop).
3. For a *quasicrystalline* target, demand λ **Pisot** (Meyer's theorem: self-similar Meyer
   ⇒ Pisot/Salem) and ideally a **unit** (so the internal/perp space is Euclidean and the
   window is a clean Rauzy fractal). Golden φ, silver 1+√2, and the plastic number are the
   "safe" exemplars; a Salem value is the boundary case the Pisot conjecture warns about.
The right/left PF eigenvectors are also data we use: right = **tile frequencies**, left =
**relative tile areas** of the projected monotile cluster.

### (b) Recognizability ⇒ our non-factorization certificate
The crux of a strict-extension / monotile argument is showing the tiling space admits **no
competing decomposition** — no periodic factor, no rival hierarchy. That is *literally*
**recognizability / unique composition**:
- **Mossé**: an aperiodic primitive substitution is recognizable — there is a finite radius
  ℓ within which local data fixes every supertile cut, so de-substitution is **unique**.
- **Solomyak**: for primitive self-affine tilings, **UCP ⇔ aperiodicity**. So proving our
  layer is aperiodic *is* proving unique de-substitution, and vice versa.
- The phenomenon is precisely **"locally indistinguishable, globally forced"**: ℓ can exceed
  any single supertile, so no bounded patch betrays the hierarchy — yet the hierarchy is
  determined. That non-existence of an alternative factorization is our certificate.
- **Mozes / Goodman-Strauss** then turn that certificate into **finite local matching
  rules** — which is exactly what we need to realize the hierarchy as a *single tile with
  edge/decoration rules* (a monotile). Goodman-Strauss "covers all known hierarchical
  aperiodic tilings," so our designed-then-projected layer should fall under it provided we
  keep recognizability.
Practical check: verify our substitution is **primitive + aperiodic** (equivalently UCP),
which simultaneously (i) certifies non-factorization and (ii) guarantees matching rules
exist to enforce the shadow monotile.

### (c) Substitution ⇄ model-set duality ⇒ the two "charts" of theory space
Our "design the higher layer, then project down" is exactly the **substitution chart ⇄
cut-and-project chart** duality:
- **Substitution / physical chart:** the expanding inflation by λ — where we *design* the
  hierarchy and read off the eigenvalue audit.
- **Model-set / internal chart:** the projection-down — where the **window (Rauzy fractal)**
  lives in the internal space spanned by the **Galois conjugates of λ**, and "projecting
  down" = slicing the higher lattice through that window.
- The change of charts is **Thurston/Frettlöh Galois (star) duality**: physical inflation λ
  ↔ internal contraction by its conjugates; the window is the attractor of the *dual*
  contractive IFS. Existence of a genuine window (interior ≠ ∅) is **equivalent to
  pure-point diffraction** and to the **model-set property** — the same condition the **Pisot
  substitution conjecture** is about. So: choosing a **Pisot-unit λ** makes both charts
  consistent (Euclidean internal space, clean window), and our projected-down object is then
  provably a **regular model set / pure-point-diffractive** monotile tiling.

**One-line synthesis.** Pick a **primitive, aperiodic** higher-layer substitution with a
**Pisot-unit inflation factor λ**; the **PF eigenvalue λ^d** is the eigenvalue audit,
**recognizability/UCP** is the non-factorization certificate (and yields matching rules for
the shadow monotile), and **Galois/star duality** is the precise dictionary between the
substitution chart we design in and the cut-and-project chart we project down from.
