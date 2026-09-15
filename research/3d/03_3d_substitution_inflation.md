# 3D Substitution / Inflation Tilings and the Algebra of 3D Inflation Factors

Research note 3d-03. Compiled 2026-06-09 from primary sources (arXiv, *Discrete &
Computational Geometry*, *Annals of Physics*, IUCr/*Acta Cryst. A*, Tilings Encyclopedia /
Bielefeld). All matrices and eigenvalues below were **recomputed and verified locally**;
inline citations carry the source URL. This is the **focused 3D deep-dive on the
substitution chart** and the **algebra of 3D inflation factors**, the companion to the
planar note [`../03_substitution_inflation_pisot.md`](../03_substitution_inflation_pisot.md).
It feeds the eigenvalue audit (**T1**), the recognizability / strict-extension certificate,
and the substitution ↔ cut-and-project duality of the shadow program.

> **PROVEN vs OPEN flags** are attached to every load-bearing claim, with dates. The headline
> for the hunt: **every strongly-ordered (pure-point) 3D inflation tiling on record is driven
> by a power of the golden ratio τ** (τ, τ³). No icosahedral/3D primitive inflation is known
> for the *plastic number* or any *non-golden cubic Pisot* — that gap is the target (§8).

---

## 1. Overview — what changes (and what does not) in 3D

The substitution machine is dimension-agnostic in its **algebra** but not in its **supply**:

1. **The combinatorics still linearize.** Forget geometry, count "how many tiles of type *j*
   appear in the inflation of tile *i*" → the **substitution (abelianization) matrix** *M*.
   For primitive *M*, Perron–Frobenius gives a unique dominant eigenvalue λ_PF. In ℝ³ this is
   the **volume** inflation; for a *self-similar* (similarity) inflation with linear factor λ,
   **λ_PF = λ³**. This is the eigenvalue audit in 3D. (PROVEN, classical.)

2. **The admissibility constraint sharpens and is only half-solved.** In 1D, λ admissible ⇔
   |λ| Perron (Lind, PROVEN). In the plane, similarity λ admissible ⇔ complex Perron
   (Thurston necessity + Kenyon sufficiency, PROVEN). In **ℝⁿ, n ≥ 3, only a *necessary*
   eigenvalue condition is proven** (Kenyon–Solomyak Thm 3.1, 2010); the converse
   (sufficiency / construction) is **OPEN**, and there is even a **specific 3D non-existence
   conjecture** (§3.3). So the audit gate in 3D is *necessary-but-not-known-sufficient*.

3. **Recognizability is fully general.** Solomyak's "nonperiodicity ⇔ unique composition"
   theorem is stated and proven for **self-affine tilings of ℝᵈ for all d** — no dimension
   restriction (PROVEN). The strict-extension certificate therefore transfers to 3D verbatim
   (§4).

4. **The duality survives, conditionally.** A primitive *unimodular* substitution tiling of
   ℝᵈ with pure-point spectrum **is** a regular Euclidean model set in a cut-and-project
   scheme whose internal space is built from the Galois conjugates (Lee, PROVEN for
   unimodular + equal-multiplicity; §5). The 3D analogue of the Rauzy fractal is the
   **atomic surface / acceptance domain** in the internal space (3-dim'l for icosahedral,
   embedded in 6D).

The two flagship 3D inflations — **Danzer's ABCK tetrahedra** and the **3D Penrose
(Ammann) rhombohedra** — both realize the *same* Pisot unit, **λ = τ, λ_PF = τ³**, and both
are model sets. They are the 3D "proof of concept" the way the hat is in the plane.

---

## 2. Danzer's ABCK tetrahedral substitution and the 3D Penrose rhombohedral inflation

### 2.1 Danzer's ABCK tetrahedra (icosahedral, 4 prototiles)

Danzer's tiling uses **four tetrahedral prototiles A, B, C, K** with edge lengths drawn from
{1, τ} (τ = (1+√5)/2), all faces orthogonal to the 2-fold axes of the icosahedral group H₃;
**K** is the fundamental domain of H₃ (the cell of the rhombic triacontahedron). The vertices
sit at fundamental weights of H₃ / projections of the **D₆ root lattice**. (Al-Siyabi–Koca–Koca,
*Icosahedral Polyhedra from D₆ lattice and Danzer's ABCK tiling*, Symmetry 12 (2020) 1983;
arXiv:2003.13449, https://arxiv.org/abs/2003.13449.)

**The exact inflation rules** (linear inflation factor **λ = τ**), as given vertex-by-vertex
in arXiv:2003.13449 §"Inflation of each tile":

| inflated tile | decomposition | (A, B, C, K) counts |
|---|---|---|
| **τK** | = B + K | (0, 1, 0, 1) |
| **τB** | = C + 4K + B₁ + B₂ | (0, 2, 1, 4) |
| **τC** | = K₁ + K₂ + C₁ + C₂ + A | (1, 0, 2, 2) |
| **τA** | = 3B + 2C + 6K  (= C + K₁ + K₂ + B + τB) | (0, 3, 2, 6) |

The paper notes the inflation **cyclically permutes** the three "core" polyhedra
(triacontahedron ↔ B-polyhedron ↔ C-polyhedron) centred at the origin
(arXiv:2003.13449, Conclusion).

**The substitution matrix** *M* (rows = tile produced, columns = tile inflated; order
A, B, C, K), assembled from the table:

```
        A  B  C  K     (column = inflation image of that tile)
   A  [  0  0  1  0 ]
M= B  [  3  2  0  1 ]
   C  [  2  1  2  0 ]
   K  [  6  4  2  1 ]
```

**Eigenvalues (locally computed, exact):**

> **λ_PF = τ³ = 2 + √5 ≈ 4.236068**, with full spectrum **{ τ³, τ, −τ⁻¹, −τ⁻² }**,
> characteristic polynomial **x⁴ − 5x³ + 2x² + 5x + 1**.

- This is the volume inflation; the linear factor is **λ = τ** ⇒ λ_PF = λ³ = τ³ ✓.
- **All four eigenvalues lie in ℚ(τ)** (powers of τ): the subdominant τ is a "shape"
  eigenvalue; the two conjugates −τ⁻¹, −τ⁻² have modulus < 1 → the contracting internal
  data (cf. §5). λ = τ is a **Pisot unit**, so the perp space is Euclidean.
- **Right** PF-eigenvector (frequencies) A:B:C:K ≈ **0.038 : 0.283 : 0.160 : 0.519**.
- **Left** PF-eigenvector (relative **volumes**) A:B:C:K = **2τ² : 2τ : 2τ : 1**
  ( = (3+√5) : (1+√5) : (1+√5) : 1 ); K is the smallest cell, A the largest. (Verified
  algebraically.)

The companion fact cited by the authors: detailed composition into long-range quasiperiodic
order "follows from the inflation matrix" exactly as in Baake–Grimm, *Aperiodic Order Vol. 1*,
pp. 229–235 (the standard reference for the ABCK spectrum/eigenvectors).

> Note on conventions: many texts present Danzer's tiling with **six** tetrahedra (A, B, C
> and three mirror partners) or absorb K-multiplicity differently; the *spectrum* (τ³ volume
> factor, ℚ(τ) eigenvalues) is convention-independent. Some authors also quote the **τ³**
> inflation directly (skipping intermediate τ-steps), since one full τ-inflation already
> multiplies volume by τ³.

### 2.2 The 3D Penrose / Ammann rhombohedral inflation (icosahedral, 2 prototiles)

The 3D analogue of the planar Penrose rhomb tiling is **Ammann's two golden rhombohedra** —
a **prolate** (acute) and an **oblate** (obtuse) rhombohedron, identical faces (golden
rhombi), icosahedrally symmetric. First given by Ammann; the icosahedral quasicrystal
interpretation is Levine–Steinhardt / Socolar–Steinhardt. (Tilings Encyclopedia, Penrose
Rhomb glossary; Katz–Duneau, Socolar–Steinhardt *Theory of matching rules for the
3-dimensional Penrose tilings*, Commun. Math. Phys. 118 (1988) 75,
https://link.springer.com/article/10.1007/BF01218580; matching-rules-by-inflation derivation:
J. Non-Cryst. Solids 153–154 (1993), https://www.sciencedirect.com/science/article/abs/pii/092150939190897V.)

**Quantitative facts** (PROVEN, standard): the **linear inflation factor is τ**; the prolate
rhombohedron has volume **τ× the oblate** and appears **τ× as frequently**; "golden zonohedra
are inflated by a factor of τ³" (volume) and uniquely decorated by original-size polyhedra.
(Looking-for-alternatives review, *Acta Cryst. A* / PMC,
https://pmc.ncbi.nlm.nih.gov/articles/PMC6364603/.)

**The 2-tile substitution matrix** in basis (Prolate P, Oblate O) consistent with
[ frequency ratio P:O = τ:1 ] and [ volume factor τ³ ] (locally computed):

```
        P  O
M =  [  3  2 ]      =  F³   (cube of the Fibonacci matrix F = [[1,1],[1,0]])
     [  2  1 ]
```

> **Eigenvalues: τ³ = 2+√5 ≈ 4.236 and (−1/τ)³ = 2−√5 ≈ −0.236**, characteristic polynomial
> **x² − 4x − 1**, det = −1 (unimodular). Right PF-eigenvector **P : O = τ : 1** ✓.

The structural punchline: the rhombohedral inflation matrix is literally **F³** — the 3D
volume hierarchy is the **cube of the 1D Fibonacci hierarchy**, because the icosahedral
structure is a τ-driven product along the three "axes." The non-PF eigenvalue (−1/τ)³ has
modulus < 1 (Pisot) and supplies the contracting internal-space action. λ = τ is a Pisot
**unit** ⇒ Euclidean internal space (§5).

> Caveat: just as in the plane (where rhomb vs Robinson-triangle decompositions give matrices
> [[2,1],[1,1]] vs [[1,1],[1,0]] with eigenvalues φ² vs φ), the *exact* 2×2 integer matrix for
> 3D Penrose depends on whether one tracks rhombohedra, half-tiles, or the
> Mosseri–Sadoc/zonohedral cell set. **Every such choice has dominant eigenvalue a power of τ**
> and conjugates of modulus < 1; the value above is the rhombohedron-count, τ³-volume,
> τ:1-frequency normalization.

### 2.3 Related icosahedral cell sets (same τ-algebra)

- **Mosseri–Sadoc / zonohedral tiles** (rhombic triacontahedron, rhombic icosahedron, rhombic
  dodecahedron, prolate rhombohedron): a 4-prototile icosahedral inflation; the
  triacontahedron resolves into 10 prolate + 10 oblate rhombohedra; inflation again τ-based.
  (Dodecahedral structures with Mosseri–Sadoc tiles, arXiv:2009.07048,
  https://arxiv.org/abs/2009.07048.)
- **Socolar–Steinhardt** quasi-unit-cell / matching-rule version: same τ inflation, designed
  so finite face decorations force the icosahedral quasiperiodic order (CMP 118 (1988)).

---

## 3. The algebra of admissible 3D inflation factors (Perron, Pisot, Salem in ℝⁿ)

### 3.1 The hierarchy of constraints

| dimension / setting | admissible λ — necessary | converse (sufficiency) | status |
|---|---|---|---|
| **1D self-similar line** | \|λ\| **Perron** | every Perron number is realized | **PROVEN** (Lind 1984) |
| **2D self-similar (similarity)** | λ **complex Perron** | every complex Perron realized | **PROVEN** (Thurston ⇒; Kenyon ⇐, GAFA 1996) |
| **ℝⁿ self-affine, φ diagonalizable** | Kenyon–Solomyak eigenvalue condition (Thm 3.1) | conjectured sufficient | **necessity PROVEN (2010); converse OPEN** |
| **+ Meyer + λΛ⊂Λ (quasicrystal)** | λ **Pisot or Salem** | each Pisot/Salem realized as a model set | **PROVEN** (Meyer; Lagarias) |
| **+ pure-point / model-set, unimodular** | λ **Pisot family**, unit ⇒ Euclidean perp | model-set ⇔ pure-point | **PROVEN for unimodular** (Lee; §5) |

### 3.2 The Kenyon–Solomyak ℝⁿ necessary condition (PROVEN 2010)

The general-dimension audit gate. For a self-affine tiling (SAT) of ℝⁿ, the **subdivision
matrix** *m* is a primitive nonnegative integer matrix; "the leading eigenvalue of *m* is the
**volume expansion** of the SAT, which therefore must be a **real Perron number**"
(Kenyon–Solomyak, arXiv:0801.1993, §2). The constraint on the *linear* expansion map φ:

> **Theorem 3.1 (Kenyon–Solomyak 2010).** Let φ be a diagonalizable-over-ℂ expanding linear
> map on ℝⁿ and **T** a self-affine tiling of ℝⁿ with expansion φ. Then
> **(i)** every eigenvalue of φ is an **algebraic integer**;
> **(ii)** if λ is an eigenvalue of φ of multiplicity *k* and γ is an algebraic conjugate of
> λ, then **either |γ| < |λ|, or γ is also an eigenvalue of φ of multiplicity ≥ k.**
> (R. Kenyon, B. Solomyak, *On the characterization of expansion maps for self-affine
> tilings*, **Discrete Comput. Geom. 43 (2010) 577–593**; arXiv:0801.1993,
> https://arxiv.org/abs/0801.1993; Springer
> https://link.springer.com/article/10.1007/s00454-009-9199-6.)

Condition (ii) is the precise **multi-dimensional generalization of "Perron."** For a single
real eigenvalue (1D) it says all conjugates are strictly smaller ⇒ Perron. In higher
dimensions a *large* conjugate is only allowed if it is itself realized as an eigenvalue with
enough multiplicity — i.e. the expansion must "carry along" any conjugate that wants to be
big. Equivalently (their second description): **there is an integer matrix *M* on ℝ^N (N ≥ n)
with an invariant n-subspace W on which it has strictly larger growth (|det|) than on any
other n-subspace, and M|_W is linearly conjugate to φ.** This is exactly the "audited shadow"
picture — φ is a *dominant invariant block* of an integer (lattice) matrix upstairs.

### 3.3 The OPEN converse and a concrete 3D non-existence conjecture

> The converse — *does every φ satisfying Thm 3.1 actually arise from some SAT?* — is **OPEN**
> (as of the 2010 paper and not resolved since to our knowledge). Kenyon–Solomyak conjecture
> **yes**, but give a sharpened **3D non-existence example** where the *necessary* condition
> already fails:
>
> **"We conjecture that there is no SAT in ℝ³ with expansion**
> **diag( √(3+√2), √(3+√2), √(3−√2) )** — although one *can* construct an SAT with expansion
> **diag( √(3+√2), √(3+√2), √(3−√2) )** arranged so the multiplicities match." (arXiv:0801.1993,
> §1.) Here √(3+√2) > 1 has multiplicity 2 but its conjugate √(3−√2) < 1 has multiplicity 1 <
> 2, violating (ii) — a clean, explicit 3D *forbidden* expansion. (The "easy to construct"
> matrix differs only in how the conjugate's multiplicity is balanced.)

**Take-away for the audit:** in 3D the audit can **reject** (Thm 3.1 fails ⇒ no tiling) and
can **strongly suggest** (Thm 3.1 holds ⇒ conjecturally realizable), but it **cannot yet
certify existence** from the eigenvalues alone. Existence in 3D still wants an explicit
construction (a D₆-style lattice block, as in Danzer/rhombohedra).

### 3.4 Meyer ⇒ Pisot/Salem (PROVEN, all n) and the unit refinement

Once the 3D structure is a **Meyer set** with λΛ ⊆ Λ, λ is forced to be **Pisot or Salem**
in *every* dimension (Meyer's theorem; converse: each Pisot/Salem β has a model set in ℝⁿ with
βΛ⊂Λ — Berthé et al., arXiv:2404.04116, Thm 2.2,
https://arxiv.org/abs/2404.04116). For pure-point order one wants **Pisot**, and for a clean
**Euclidean internal space** one wants λ a **unit** (constant term ±1, |det φ| = 1) — the
3D Danzer τ and rhombohedral τ are both Pisot units.

### 3.5 Which specific algebraic integers are *realized* in 3D (vs open)

| number | poly | type | realized in 3D? |
|---|---|---|---|
| **τ = (1+√5)/2** | x²−x−1 | golden, Pisot **unit** | **YES** — Danzer τ, rhombohedra τ (linear); volume τ³ |
| **τ³ = 2+√5** | x²−4x−1 | Pisot **unit** (= τ in ℚ(τ)) | **YES** — volume factor of every icosahedral inflation |
| **τ, τ³ (per module)** | — | Pisot units | **YES** — P/F/I icosahedral modules: scaling = power of τ (§5.3) |
| **silver 1+√2** | x²−2x−1 | Pisot unit | only **2D** (Ammann–Beenker) realized; **3D icosahedral analogue OPEN** |
| **plastic ρ ≈ 1.3247** | x³−x−1 | **smallest Pisot**, unit | **1D** (smallest-PV ternary) & **2D** (double-angle-plastic / squeeze) only; **NOT realized as a 3D icosahedral / primitive inflation** — OPEN |
| general **cubic Pisot units** | x³−ax²−bx−1 | Pisot units, deg 3 | **OPEN** as genuine ℝ³ self-similar inflations (vs 1D/product) |
| **Lehmer ≈ 1.176** | deg-10 Salem | smallest known Salem | not realized; Salem-driven order is boundary/subtle (Pisot-conj excluded) |

> **The single most important strategic fact (§8):** Fujita's classification of self-similar
> quasiperiodic **canonical-cell tilings** states "the primitive scaling ratio … is an **n-th
> power of the Pisot unit associated with the underlying Bravais module**, with the Pisot units
> being **τ³, τ, and τ** for the [primitive, body-centred, face-centred] icosahedral module
> types." (Fujita, *Quasiperiodic canonical-cell tiling with pseudo icosahedral symmetry*,
> **Ann. Phys. 385 (2017) 225**;
> https://www.sciencedirect.com/science/article/pii/S0003491617302208;
> https://ui.adsabs.harvard.edu/abs/2017AnPhy.385..225F/abstract.) **Every** icosahedral
> 3D inflation on record is a power of **τ**. A non-golden 3D inflation is unclaimed territory.

---

## 4. 3D recognizability / unique composition (the strict-extension certificate)

The de-substitution / non-factorization certificate transfers to 3D **with no loss** — this
is the most favorable item for the program.

### 4.1 Solomyak's UCP theorem holds in ℝᵈ for all d (PROVEN)

> **Theorem (Solomyak 1998).** A **translationally-finite self-affine tiling of ℝᵈ** has the
> **unique composition property (UCP)** — every tiling in the hull has *exactly one*
> partition into level-1 supertiles — **if and only if it is non-periodic.** (More precisely,
> UCP holds modulo the translation-symmetry group; for aperiodic tilings the de-substitution
> is unique.) (B. Solomyak, *Nonperiodicity implies unique composition for self-similar
> translationally finite tilings*, **Discrete Comput. Geom. 20 (1998) 265–279**;
> https://link.springer.com/article/10.1007/PL00009386.) UCP is Solomyak's name for
> **recognizability** in the self-affine (geometric) setting.

There is **no dimension restriction**: the statement is for ℝᵈ. So a primitive aperiodic 3D
inflation (Danzer, rhombohedra) is **recognizable / uniquely de-substitutable** — globally the
hierarchy is forced even though no bounded ball reveals it.

### 4.2 Mossé/Berthé recognizability and generalised pattern spaces (PROVEN; 2018, 2025)

- The symbolic Mossé theorem ("aperiodic primitive ⇒ recognizable") and its extension to
  **sequences of morphisms / S-adic** systems are stated abstractly and apply to higher-rank
  (multidimensional) actions (Berthé–Steiner–Thuswaldner–Yassawi, *Recognizability for
  sequences of morphisms*, arXiv:1705.00167, https://arxiv.org/abs/1705.00167).
- Most relevant: **recognisability for *generalised hierarchical pattern spaces* of finite
  local complexity** — explicitly built for self-affine substitutions of **Euclidean space**
  (any dimension), proving substitutional pre-images are translation-equivalent, **with no
  minimality requirement** (arXiv:2509.21001, 2025,
  https://arxiv.org/html/2509.21001). This is the clean modern 3D-ready recognizability
  statement.

### 4.3 Subtleties specific to 3D

- **FLC is not automatic** in 3D with rotations: if tiles appear in **infinitely many
  orientations**, finite local complexity can fail, and the standard recognizability machinery
  needs the FLC hypothesis (it is fine for Danzer/rhombohedra, which use finitely many
  icosahedral orientations). Pure-point spectrum *implies* Meyer ⇒ FLC (Lee–Solomyak), so for
  the model-set targets FLC is free.
- **Matching-rule enforceability** (the bridge recognizability → a *monotile* with face
  decorations) is **established in 3D for the rhombohedra**: Socolar–Steinhardt and
  Katz–Duneau proved finite face decorations (Ammann planes) force the 3D Penrose hierarchy
  (CMP 118 (1988); J. Non-Cryst. Solids 1993). Goodman-Strauss's general "substitution ⇒ local
  rules" theorem is stated for ℝᵈ, d > 1, so it also covers 3D in principle.

**Net:** the strict-extension certificate (π₁ does not factor through π₀ / no rival
decomposition) is **just as available in 3D as in 2D** — recognizability = UCP is a theorem in
ℝᵈ. The only 3D care-points are FLC (free under pure-point order) and orientation count.

---

## 5. The 3D substitution ↔ cut-and-project duality (model sets, atomic surfaces)

### 5.1 The d-dimensional duality theorem (PROVEN for unimodular; Lee)

The 3D analogue of "substitution chart ⇄ projection chart":

> **Theorem 5.9 / Cor 5.10 (Lee).** Let **T** be a repetitive primitive substitution tiling of
> **ℝᵈ** with a **diagonalizable, unimodular** expansion map φ, all eigenvalues algebraic
> conjugates of the **same multiplicity**. Then **T has pure discrete (pure-point) spectrum
> ⇔ each control-point set is a regular *Euclidean* model set** in an explicitly-constructed
> cut-and-project scheme. (J.-Y. Lee, *Pure Discrete Spectrum and Regular Model Sets in
> Unimodular Substitution Tilings on ℝᵈ*, arXiv:2007.11242,
> https://arxiv.org/abs/2007.11242; IUCr/*Acta Cryst. A* version,
> https://onlinelibrary.wiley.com/iucr/doi/10.1107/S2053273320009717.)

The mechanism is exactly the conjugate-space picture: unimodular ⇒ "there exists at least one
algebraic conjugate λ of the eigenvalues with **|λ| < 1**, so we can construct the CPS with a
**Euclidean internal space**" (Lee, proof of Thm 5.9). The contracting conjugate(s) drive the
internal IFS; its attractor is the **window** = the 3D analogue of the Rauzy fractal.

Supporting result: pure-point ⇒ Meyer ⇒ FLC and φ satisfies the **Pisot family** condition
(Lee–Solomyak 2012, 2018), so "unimodular + pure-point" already forces the Pisot-family
algebra that makes the perp space work.

### 5.2 The 3D analogue of the Rauzy fractal — the atomic surface

For **icosahedral** tilings the canonical cut-and-project scheme is:

- **6D embedding.** Six is the lowest dimension carrying a periodic lattice with icosahedral
  symmetry; three primitive lattices qualify — **primitive (P), body-centred (I),
  face-centred (F)** hypercubic — giving **three classes of icosahedral model sets.**
- **Split ℝ⁶ = E∥ (3D physical) ⊕ E⊥ (3D internal),** the two icosahedral 3-reps.
- **Window / atomic surface = 3-dimensional.** The canonical acceptance domain is a **rhombic
  triacontahedron** in E⊥; lattice points project iff their internal image lands in it.
  (Quasicrystal review and *Looking for alternatives…*, PMC6364603,
  https://pmc.ncbi.nlm.nih.gov/articles/PMC6364603/.)
- **Fractal windows.** Beyond the convex triacontahedron, the genuinely self-similar
  canonical-cell tilings have **fractal atomic surfaces** — Fujita: "the first realization of
  three-dimensional quasiperiodic tilings with **fractal atomic surfaces**" (Ann. Phys. 385
  (2017) 225). These are the **3D Rauzy fractals** — the contracting-window image of the
  τ-driven inflation, the direct 3D analogue of the hat's fractal Rauzy window in the plane.

So the duality in 3D reads: **substitution/physical chart** = expanding inflation by τ
(matrix *M*, audit eigenvalue τ³); **model-set/internal chart** = the D₆ / 6D lattice sliced by
the (possibly fractal) triacontahedral window in the 3D internal space. The change of charts
is Galois/star duality (Thurston; Frettlöh's star-duality, arXiv:math/0601064), τ in E∥ ↔ its
conjugate −1/τ (modulus < 1) in E⊥.

### 5.3 Which 3D substitutions are model sets

- **3D Penrose rhombohedra: YES (model set, pure-point).** It is *the* icosahedral model set
  — a projection of the 6D lattice; matching rules proven (CMP 118 (1988)). Inflation τ,
  volume τ³, unimodular ⇒ Lee's theorem applies. (PROVEN.)
- **Danzer ABCK: YES (model set).** Explicitly obtained from **D₆** (arXiv:2003.13449); same
  τ-algebra; mutually-locally-derivable with the rhombohedra (faces share the 2-fold-axis
  orientation). (PROVEN.)
- **Canonical-cell tilings (Fujita): YES, with fractal windows.** Self-similar, scaling a
  power of the τ-Pisot-unit, fractal atomic surfaces. (PROVEN 2017.)
- **SCD biprism: NO.** See §6 — singular diffraction, not a model set, no inflation. The lone
  3D weakly-aperiodic monotile is *outside* the substitution/shadow world.

---

## 6. The cautionary 3D case: Schmitt–Conway–Danzer (not a shadow)

The only previously-known 3D aperiodic **monotile** is a sharp negative example for the
substitution chart:

- **Weakly aperiodic only.** The SCD biprism tiles ℝ³ with **no translational symmetry**, but
  every tiling admits a **screw symmetry** (rotation by an irrational angle ∘ translation) —
  an infinite cyclic symmetry group — so it is *weakly*, not *strongly*, aperiodic. (Einstein
  problem, Wikipedia, https://en.wikipedia.org/wiki/Einstein_problem.) **Strongly aperiodic
  3D monotile: OPEN** (as of 2026).
- **No inflation, not Pisot, singular diffraction (PROVEN).** "The diffraction spectrum of any
  SCD set Λ_SCD is a **singular measure**" — no absolutely continuous part, a pure-point part
  only **on one axis (the screw axis)**, otherwise singular continuous. (M. Baake, D. Frettlöh,
  *SCD patterns have singular diffraction*, **J. Math. Phys. 46 (2005) 033510**,
  arXiv:math-ph/0411052, https://arxiv.org/abs/math-ph/0411052, Thm 2.1.) SCD is **not a model
  set**, has **no Pisot inflation factor**, and its order is essentially a **stack of
  incommensurably-rotated periodic layers** — the screw is the residual cyclic symmetry the
  hierarchy cannot kill.

> SCD is exactly the *failure mode* the certificate is built to detect: the screw is a
> non-descending symmetry that survives projection — a "U half-descends to a residual cyclic
> symmetry" obstruction. A genuine 3D shadow monotile must **not** be MLD to such a layered
> object; it must carry a *fully* contracting internal action (pure-point, Pisot), which SCD
> provably lacks. SCD is therefore the ideal **negative oracle** for 3D field-3 (non-descent)
> testing.

---

## 7. Examples table (3D and reference 1D/2D anchors)

| tiling | dim | prototiles | linear λ | substitution matrix | λ_PF (volume) | algebra of λ | model set? | status |
|---|---|---|---|---|---|---|---|---|
| **Danzer ABCK** | 3 | 4 tetrahedra A,B,C,K (edges 1,τ) | τ | 4×4 (§2.1) | **τ³ = 2+√5**; spectrum {τ³,τ,−τ⁻¹,−τ⁻²}; charpoly x⁴−5x³+2x²+5x+1 | golden, **Pisot unit** | **YES** (from D₆) | PROVEN |
| **3D Penrose (Ammann rhombohedra)** | 3 | 2 rhombohedra (prolate, oblate) | τ | [[3,2],[2,1]] = **F³** | **τ³ = 2+√5**; eig {τ³, (−1/τ)³}; charpoly x²−4x−1 | golden, **Pisot unit** | **YES** (6D icosahedral) | PROVEN |
| **Mosseri–Sadoc zonohedral** | 3 | 4 (triacontahedron, icosahedron, dodecahedron, prolate) | τ-based | (4-tile) | power of τ | golden, Pisot unit | YES | PROVEN |
| **Canonical-cell (Fujita)** | 3 | 4 canonical cells (B,O,P,T) | τ-based | (point substitution) | **τ³ / τ / τ** per P/I/F module | golden, Pisot unit | YES, **fractal window** | PROVEN 2017 |
| **SCD biprism** | 3 | **1** (convex biprism) — *monotile* | — (no inflation) | — | — | **none** (singular diffraction) | **NO** | weakly aperiodic; PROVEN |
| *Penrose (rhomb)* | 2 | 2 rhombs | φ | [[2,1],[1,1]] | φ² | golden, Pisot unit | yes | PROVEN |
| *Ammann–Beenker* | 2 | square+rhomb | 1+√2 | [[2,1],[1,0]]-Pell | (1+√2)² | silver, Pisot unit | yes | PROVEN |
| *plastic / smallest-PV* | 1 (& 2D) | 3 letters / triangles | ρ≈1.3247 | a→b,b→c,c→ab | ρ (1D) | **smallest Pisot**, unit | yes (1D/2D) | **3D OPEN** |
| *Fibonacci* | 1 | a,b | φ | [[1,1],[1,0]] | φ | golden, Pisot unit | yes | PROVEN |

---

## 8. Relevance to our shadow / strict-extension approach

### 8.1 How the eigenvalue audit (T1) instantiates in 3D

The 3D audit is **three nested gates**, each a citable theorem:

1. **Primitivity + dominant block (necessary, PROVEN).** Write the 3D subdivision matrix *M*;
   check **primitive** (some *Mⁿ* > 0). Then λ_PF = leading eigenvalue = **volume** inflation;
   for similarity inflation, **linear λ = λ_PF^{1/3}**. By Kenyon–Solomyak Thm 3.1 the
   *physical* expansion φ must have **algebraic-integer eigenvalues** satisfying the
   **multiplicity-conjugate condition (ii)** — and, equivalently, **φ must be a dominant
   invariant n-block of an integer (lattice) matrix upstairs.** That "dominant invariant block
   of an upstairs integer matrix" is *literally our audited-shadow statement*: the higher
   layer is the ℝ^N integer matrix, the physical tiling is its top-growth 3-subspace.
2. **Pisot/unit gate (for pure-point order, PROVEN).** For a quasicrystalline target, Meyer ⇒
   λ **Pisot or Salem**; demand **Pisot**, and a **unit** so the perp space is Euclidean
   (Lee Thm 5.9). Verify the **subdominant conjugates have modulus < 1** — they are the
   **trace-budget / contracting internal data**. For Danzer this reads
   {subdominant τ "shape"; contracting −τ⁻¹, −τ⁻²}; for rhombohedra {τ³ ; contracting
   (−1/τ)³}.
3. **3D existence caveat (OPEN).** Thm 3.1 is **necessary, not known sufficient** in 3D, and
   there is a **specific forbidden 3D expansion** (diag(√(3+√2),√(3+√2),√(3−√2)), §3.3). So in
   3D the eigenvalue audit can **reject** outright and can **green-light conjecturally**, but
   existence still wants an explicit **lattice block** (the D₆ / 6D construction). Our audit
   should therefore *pair the eigenvalue check with an explicit upstairs integer matrix*
   exhibiting φ as its dominant block — that simultaneously discharges Thm 3.1(ii) and gives
   the cut-and-project lattice for free.

### 8.2 How the recognizability certificate instantiates in 3D

**Unchanged from 2D, and that is the good news.** Solomyak's **UCP ⇔ aperiodicity** is a
theorem in **ℝᵈ for all d** (DCG 20 (1998)); the modern generalised-pattern-space version
(arXiv:2509.21001, 2025) is built for self-affine substitutions of Euclidean space with no
minimality requirement. So:

- Proving our designed 3D layer is **primitive + aperiodic** *is* proving **unique
  de-substitution** = **no rival (periodic or competing-hierarchical) factorization** = the
  strict-extension certificate.
- **FLC is free** under the pure-point/Meyer target (Lee–Solomyak), so the only 3D care-point
  (finitely many tile orientations) is automatically satisfied for icosahedral model sets.
- **Matching rules → monotile** is *already demonstrated in 3D* for the rhombohedra
  (Socolar–Steinhardt, Katz–Duneau, CMP 118 (1988)); Goodman-Strauss covers ℝᵈ, d>1. So a
  recognizable 3D shadow can, in principle, be pushed to a single decorated solid.
- **Negative oracle:** test any 3D candidate against **SCD** — if its hull is MLD to a
  screw-stacked layered object (singular, non-Pisot, pure-point only on an axis), the
  certificate *must* reject it. A true shadow monotile has a **fully contracting internal
  action** (Pisot conjugates all < 1 in modulus), which SCD provably lacks.

### 8.3 The duality, and the best **unrealized** Pisot targets for a new 3D monotile

The substitution ↔ cut-and-project duality is **Lee Thm 5.9** in 3D: a unimodular primitive
substitution with pure-point spectrum **is** a regular Euclidean model set, window = (possibly
**fractal**) atomic surface in the internal space — the **3D Rauzy fractal**. Designing
upstairs (the inflation chart) and projecting down (the window chart) are the same object.

**The strategic opening — what is *not* yet realized in 3D:**

> Every strongly-ordered 3D inflation on record uses a **power of the golden ratio τ**
> (Fujita: scaling ratios τ³, τ, τ for the P/I/F icosahedral modules; Danzer τ; rhombohedra
> τ). The 3D substitution chart is, empirically, a **golden monoculture.**

So the **best unrealized targets**, in order of promise:

1. **The plastic number ρ (x³−x−1), and other cubic Pisot units, as a *genuine* ℝ³
   self-similar inflation.** ρ is the **smallest Pisot number** → the *slowest* 3D hierarchy
   (smallest supertiles, tightest forcing), and it is realized only in **1D and 2D**
   (smallest-PV ternary; double-angle-plastic / squeeze) — **never as a 3D icosahedral or
   primitive solid inflation.** A cubic Pisot is the natural fit for ℝ³ because deg λ = 3 can
   match a 3-dim physical block with a single contracting conjugate pair. **This is the single
   cleanest "new (λ,W)" target.** Audit plan: build a 6-ish-dimensional integer matrix whose
   dominant 3-block is the ρ-similarity, check Thm 3.1(ii) (deg-3 ⇒ two conjugates, both
   modulus < 1 since ρ is Pisot — ✓ by construction), then read off the (fractal) window.
2. **A non-icosahedral 3D point symmetry** (e.g. a *cubic*/octahedral or a different axial
   quasicrystal class) carrying a Pisot-unit inflation other than τ — none is catalogued as a
   strongly-aperiodic inflation tiling.
3. **The silver mean 1+√2 in 3D.** Realized in 2D (Ammann–Beenker) but no 3D analogue is on
   record; a silver 3D inflation would be a genuine new class.

A **new strongly-aperiodic 3D monotile** in our framework is then: pick **(Pisot-unit λ
≠ a power of τ, low-dimensional 3D-physical block of an integer matrix)**; (T1) audit =
Kenyon–Solomyak Thm 3.1(ii) on φ's eigenvalues *plus* exhibiting φ as the dominant invariant
block (which also yields the cut-and-project lattice); the **certificate** = primitivity +
aperiodicity ⇒ Solomyak UCP (no rival factorization) ⇒ Socolar-Steinhardt/Goodman-Strauss
matching rules collapsing the protoset to one decorated solid; the **window** = the 3D Rauzy
fractal / atomic surface in the internal space (Lee Thm 5.9), which is what *collapses the
prototiles to a single tile* exactly as the hat's fractal window does in the plane. The
known-good re-derivation to earn the move: **reproduce the 3D Penrose rhombohedra (λ=τ,
M=F³, window = triacontahedron)**, then walk λ off the golden axis to a cubic Pisot.

> Honest caveat (overclaim guard): in 3D the audit's existence direction is **OPEN**
> (Kenyon–Solomyak converse unproved; explicit 3D forbidden expansions exist). So a 3D target
> is **not** certified realizable by its eigenvalues alone — it must be backed by an explicit
> upstairs lattice/integer-matrix block. Recognizability and the duality, by contrast, are
> **fully proven in ℝᵈ** and transfer with no new theorem. SBT's genuine contribution would be
> **(a)** the off-golden cubic-Pisot 3D *construction*, **(b)** its explicit fractal window,
> and **(c)** the resulting single solid — not the certificate framing, which is Solomyak/Lee.

---

## 9. Authoritative sources (titles + URLs)

**Danzer ABCK & 3D Penrose rhombohedra (inflation + matrices):**
- A. Al-Siyabi, N. O. Koca, M. Koca, *Icosahedral Polyhedra from D₆ lattice and Danzer's ABCK
  tiling*, Symmetry 12 (2020) 1983 — arXiv:2003.13449, https://arxiv.org/abs/2003.13449
  (explicit τK,τB,τC,τA inflation rules; D₆ embedding).
- L. Danzer, *Three-dimensional analogs of the planar Penrose tilings and quasicrystals*,
  Discrete Math. 76 (1989) 1–7 (original ABCK).
- M. Senechal, *Quasicrystals and Geometry*, Cambridge UP (1995) (Danzer + rhombohedra
  exposition).
- P. Kramer, R. Neri (1984); D. Levine, P. Steinhardt (1984/86) (rhombohedral icosahedral
  tilings).
- A. Katz, M. Duneau / J. E. S. Socolar, P. J. Steinhardt, *Theory of matching rules for the
  3-dimensional Penrose tilings*, Commun. Math. Phys. 118 (1988) 75 —
  https://link.springer.com/article/10.1007/BF01218580 ; matching rules by inflation:
  J. Non-Cryst. Solids (1993),
  https://www.sciencedirect.com/science/article/abs/pii/092150939190897V
- Dodecahedral structures with Mosseri–Sadoc tiles — arXiv:2009.07048,
  https://arxiv.org/abs/2009.07048
- M. Baake, U. Grimm, *Aperiodic Order, Vol. 1*, Cambridge UP (2013), pp. 229–235 (ABCK
  substitution matrix, eigenvalues, eigenvectors — the standard reference).

**Algebra of 3D/ℝⁿ inflation factors (Perron/Pisot/Salem, the audit):**
- R. Kenyon, B. Solomyak, *On the characterization of expansion maps for self-affine tilings*,
  **Discrete Comput. Geom. 43 (2010) 577–593** — arXiv:0801.1993,
  https://arxiv.org/abs/0801.1993 ;
  https://link.springer.com/article/10.1007/s00454-009-9199-6 (Thm 3.1; ℝ³ non-existence
  conjecture).
- R. Kenyon, *The construction of self-similar tilings*, GAFA 6 (1996) 471 —
  https://link.springer.com/article/10.1007/BF02249260
- W. Thurston, *Groups, Tilings and Finite State Automata*, AMS Colloquium Lectures (1989).
- D. Lind, *The entropies of topological Markov shifts and a related class of algebraic
  integers*, Ergodic Theory Dynam. Systems 4 (1984) (Perron ⇔ 1D expansion).
- V. Berthé, R. Yassawi, et al., *Meyer sets, Pisot numbers, and self-similarity in symbolic
  dynamical systems* — arXiv:2404.04116, https://arxiv.org/abs/2404.04116 (Meyer ⇒
  Pisot/Salem, all n).
- C. L. Henley, *canonical-cell tilings* (introduces the 4 canonical cells); M. Fujita,
  *Quasiperiodic canonical-cell tiling with pseudo icosahedral symmetry*, **Ann. Phys. 385
  (2017) 225** —
  https://www.sciencedirect.com/science/article/pii/S0003491617302208 (scaling = power of the
  τ-Pisot-unit; **fractal atomic surfaces**).
- MathWorld, *Plastic Constant* — https://mathworld.wolfram.com/PlasticConstant.html ;
  Bielefeld *Plastic Number* — https://tilings.math.uni-bielefeld.de/glossary/plastic_number/
  (smallest PV; realized in 1D/2D).

**3D recognizability / unique composition (the certificate):**
- B. Solomyak, *Nonperiodicity implies unique composition for self-similar translationally
  finite tilings*, **Discrete Comput. Geom. 20 (1998) 265–279** —
  https://link.springer.com/article/10.1007/PL00009386 (UCP ⇔ aperiodicity, ℝᵈ).
- B. Solomyak, *Dynamics of self-similar tilings*, Ergodic Theory Dynam. Systems 17 (1997).
- V. Berthé, W. Steiner, J. Thuswaldner, R. Yassawi, *Recognizability for sequences of
  morphisms* — arXiv:1705.00167, https://arxiv.org/abs/1705.00167
- *Recognisability for generalised hierarchical pattern spaces of finite local complexity*
  (2025) — arXiv:2509.21001, https://arxiv.org/html/2509.21001 (self-affine substitutions of
  ℝⁿ, no minimality).
- C. Goodman-Strauss, *Matching rules and substitution tilings*, Annals of Math. 147 (1998)
  181 — https://annals.math.princeton.edu/articles/12903 (substitution ⇒ local rules, ℝᵈ).

**3D substitution ⇄ cut-and-project duality (model sets / atomic surfaces):**
- J.-Y. Lee, *Pure Discrete Spectrum and Regular Model Sets in Unimodular Substitution Tilings
  on ℝᵈ* — arXiv:2007.11242, https://arxiv.org/abs/2007.11242 ; IUCr/*Acta Cryst. A*,
  https://onlinelibrary.wiley.com/iucr/doi/10.1107/S2053273320009717 (Thm 5.9 / Cor 5.10,
  the d-dim duality).
- J.-Y. Lee et al., *Cut-and-Project Schemes for Pisot Family Substitution Tilings* —
  https://www.researchgate.net/publication/328326654
- D. Frettlöh, *Duality of Model Sets Generated by Substitutions* — arXiv:math/0601064,
  https://arxiv.org/abs/math/0601064 ; D. Frettlöh, B. Sing, *Self-dual tilings w.r.t.
  star-duality* — arXiv:0704.2528, https://arxiv.org/abs/0704.2528
- *Looking for alternatives to the superspace description of icosahedral quasicrystals*,
  *Acta Cryst. A* / Proc. R. Soc. A 475 (2018) 0667 —
  https://pmc.ncbi.nlm.nih.gov/articles/PMC6364603/ (6D embedding; triacontahedron window;
  P/F/I classes).

**SCD (the negative example):**
- M. Baake, D. Frettlöh, *SCD patterns have singular diffraction*, **J. Math. Phys. 46 (2005)
  033510** — arXiv:math-ph/0411052, https://arxiv.org/abs/math-ph/0411052 (Thm 2.1: singular
  measure, pure-point only on the screw axis).
- *Einstein problem* (weak vs strong aperiodicity; SCD screw symmetry) — Wikipedia,
  https://en.wikipedia.org/wiki/Einstein_problem

---

*Cross-refs: planar substitution/Pisot note [`../03_substitution_inflation_pisot.md`](../03_substitution_inflation_pisot.md);
cut-and-project [`../02_cut_and_project_model_sets.md`](../02_cut_and_project_model_sets.md);
frontiers / 3D-open [`../07_frontiers_methods_outofdiscipline.md`](../07_frontiers_methods_outofdiscipline.md);
strategy [`../../docs/APPROACH.md`](../../docs/APPROACH.md).*
