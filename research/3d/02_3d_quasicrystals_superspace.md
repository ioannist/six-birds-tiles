# 3D-02 — The 3D Higher Layer: Icosahedral Quasicrystals and the 6D→3D Cut-and-Project

> **Focused 3D deep-dive on the HIGHER LAYER.** This is our "shadow chart" in three dimensions. A 3D
> icosahedral quasicrystal is *literally* the irrational 3-D cut/projection of a **periodic lattice in
> 6-D** (the 6-D hypercubic lattice `ℤ⁶`, or the root lattice `D₆`). The aperiodic 3-D structure is the
> shadow; **the work is upstairs**, where everything is periodic and the only choice is *(lattice,
> window, irrational slope)*. This doc nails the 6D→3D scheme precisely, the 3D protosets (golden
> rhombohedra; Danzer ABCK tetrahedra), the occupation-domain/window structure, and the question that
> matters most for us: **could a *fractal-window reprojection* collapse a 3D icosahedral model set toward
> a SINGLE prototile**, exactly as the hat's fractal Rauzy window collapses the planar protoset to one
> tile?
>
> Companion to the broad-round doc [`../04_quasicrystals_superspace.md`](../04_quasicrystals_superspace.md)
> (physics/superspace generalities) and to [`../02_cut_and_project_model_sets.md`](../02_cut_and_project_model_sets.md)
> (the projection formalism, §7–8 of which give the hat = fractal-window collapse mechanism we extend
> here). Compiled June 2026; all URLs cited inline. **PROVEN / OPEN flagged with dates.**

---

## 1. Overview — what the "3D higher layer" concretely is

There are essentially **three** mature aperiodic-order structures in ℝ³, each a shadow of a periodic
higher lattice:

| 3D structure | "Higher layer" (periodic lattice) | Cut | Protoset downstairs |
|---|---|---|---|
| **Icosahedral** (Ammann–Kramer–Neri, "3D Penrose") | **`ℤ⁶`** primitive hypercubic | physical `E∥ = ℝ³`, internal `E⊥ = ℝ³` (so 6 = 3+3) | **2 tiles**: acute + obtuse **golden rhombohedra** |
| **Icosahedral, face-centred** (Danzer ABCK; Socolar–Steinhardt) | **`D₆`** root lattice (↔ fcc `D₃`) | `E∥ = ℝ³`, `E⊥ = ℝ³` | **4 tiles**: ABCK **tetrahedra** (or 4 zonohedra) |
| **Axial** (decagonal / dodecagonal / octagonal) | **`ℤ⁵`** (deca/dodeca) or `ℤ⁴` (octa) | 2-D quasiperiodic plane × **1 periodic axis** | 2D quasicrystal **periodically stacked** |

The icosahedral case is the genuinely 3-D one — *quasiperiodic in all three directions* — and is the
direct analogue of planar Penrose. It is the **canonical 6D→3D cut-and-project (CPS)** and is where our
shadow strategy lives in 3D. The crucial design fact: **physical space and internal space are *both* ℝ³,
and they are exchanged by the Galois/algebraic conjugation `τ ↔ σ = −1/τ`** — exactly the "Galois
conjugate space" our project notes (the contracting internal space is the home of the window). See
[Frettlöh, *Icosahedral tilings in ℝ³: the ABCK tilings*](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf)
(a Tilings-Encyclopedia author's lecture notes, our primary source here) and the survey
[Baake–Joseph–Kramer–Schlottmann, *Root lattices and quasicrystals*, J. Phys. A 23 (1990) L1037](https://iopscience.iop.org/article/10.1088/0305-4470/23/19/008).

> **One-line map to our certificate.** Higher layer = `ℤ⁶` (or `D₆`); audited descent = orthogonal
> projection `E∥`-ward through a **triacontahedral window** in `E⊥`; Pisot scale = **`τ³`**; the
> strict-extension/recognizability certificate = the substitution's eigenvalue audit `{τ³, τ, −τ⁻¹, −τ⁻³}`
> (only the Perron `τ³` expands; the rest contract — the trace budget). The "single-tile" knob = window
> shape (polytope ⇒ 2–4 tiles; **fractal ⇒ possibly 1**).

---

## 2. The canonical 6D→3D icosahedral cut-and-project scheme (PRECISE)

### 2.1 Why 6, and the icosahedral star

The icosahedral point group **`m-3̄-5̄` (`H₃` / `I_h`, order 120)** has six **5-fold axes** (the six
diameters of an icosahedron joining opposite vertices). Indexing icosahedral diffraction therefore
needs **6 integers**, not 3 — the reciprocal module is rank-6. The minimal periodic lattice carrying a
faithful icosahedral action is the **6-D hypercubic lattice `ℤ⁶`** (and its centrings `D₆`, `D₆*`): the
six standard basis vectors of `ℤ⁶` map to the six 5-fold axis directions in physical space. This is the
*reason* the embedding dimension is exactly 6. ([Quasicrystal — Wikipedia](https://en.wikipedia.org/wiki/Quasicrystal);
[Steurer & Deloudi, *Crystallography of Quasicrystals*, Springer 2009, ch. "Higher-Dimensional Approach"](https://link.springer.com/chapter/10.1007/978-3-642-01899-2_3)).

### 2.2 The splitting `ℝ⁶ = E∥ ⊕ E⊥`, with the explicit star map

Write `τ = (1+√5)/2` and its Galois conjugate `σ = −1/τ = (1−√5)/2`. The six 5-fold directions form the
**icosahedral star** — the canonical physical-space images of the `ℤ⁶` basis are (up to normalisation):

```
a₁ = (1, τ, 0)   a₂ = (−1, τ, 0)   a₃ = (0, 1, τ)
a₄ = (0, −1, τ)  a₅ = (τ, 0, 1)    a₆ = (τ, 0, −1)
```

(the 12 vertices `±aᵢ` of an icosahedron). The **internal-space (perp) images** are obtained by the
**algebraic conjugation `τ ↦ σ`** applied componentwise — i.e. the `E⊥` star is the icosahedral star
with `τ` replaced by `−1/τ`. Concretely the projector onto physical space is the `3×6` matrix whose
columns are the `aᵢ`, and the projector onto internal space is the same matrix with `τ → σ`:

```
π∥  = (1/√(2+τ)) · [ a₁ a₂ a₃ a₄ a₅ a₆ ]          (the 5-fold star, scale τ)
π⊥  = (1/√(2+σ)) · [ a₁ a₂ a₃ a₄ a₅ a₆ ]|_{τ→σ}    (the conjugate star, scale σ)
```

The **star map** `x ↦ x*` of our CPS (broad doc 02 §2.2) is exactly this conjugation `π⊥ ∘ (π∥)⁻¹`: a
lattice point's physical position determines its perp position by `τ ↔ σ`. Because `σ` is contracting
(`|σ| = 0.618… < 1`) while `τ` expands, **the internal space `E⊥` is the contracting Galois-conjugate
space where the window lives** — the 3-D analogue of the Rauzy-fractal home. ([Senechal, *Quasicrystals
and Geometry*, CUP 1995](https://www.cambridge.org/9780521575416); icosahedral basis as used in
[Al-Siyabi–Koca–Koca, *Icosahedral Polyhedra from D₆ lattice and Danzer's ABCK Tiling*, Symmetry 12 (2020) 1983, arXiv:2003.13449](https://arxiv.org/abs/2003.13449)).

The D₆ presentation makes the conjugation razor-sharp. The characteristic polynomial of the Coxeter
element of `D₆` **factors into the `E∥` and `E⊥` blocks** ([Al-Siyabi–Koca–Koca 2020, eq. (9)](https://arxiv.org/abs/2003.13449)):

```
( λ³ + σλ² + σλ + 1 )( λ³ + τλ² + τλ + 1 ) = 0
   └─ describes E⊥ (conjugate) ─┘   └─ describes E∥ (physical) ─┘
```

> **This factorisation IS the higher-layer audit in 3D.** Projecting `D₆` into either ℝ³ "violates the
> algebraic conjugation" (their words) — i.e. picks one block — and that asymmetry between the expanding
> `τ`-block (physical) and the contracting `σ`-block (internal) is precisely what makes the shadow
> aperiodic yet pure-point. It is the eigenvalue/trace-budget audit, visible as a polynomial factoring.

### 2.3 The acceptance window: the rhombic triacontahedron (occupation domain)

**Selection rule (the cut).** A lattice point `n ∈ ℤ⁶` survives iff its internal projection `n* = π⊥(n)`
lies in the **acceptance window `W ⊂ E⊥`**. For the primitive icosahedral tiling the window is

> **`W` = the projection of the 6-D unit hypercube `[0,1]⁶` into `E⊥`**, which is a **rhombic
> triacontahedron** (Kepler's triacontahedron) — a zonohedron with **icosahedral symmetry**, 30 golden-
> rhombus faces, 32 vertices, 60 edges.

This is the 3-D occupation domain. Its **faces are golden rhombi** (long:short diagonal `= τ`), and it
**dissects into exactly 10 acute (prolate) + 10 obtuse (oblate) golden rhombohedra** — a fact noticed by
**G. Kowalewski in 1935**, long before quasicrystals. ([Rhombic triacontahedron — Wikipedia](https://en.wikipedia.org/wiki/Rhombic_triacontahedron):
"the ratio of the long diagonal to the short diagonal of each face is exactly … φ"; "can be dissected
into 20 golden rhombohedra: 10 acute … and 10 obtuse"; Frettlöh notes the 10+10 fact "was noted already
in 1935 by G. Kowalewski.") The window edge length is `√(2+τ)`, volume `20τ³`, surface area `60τ`
([search consensus; cf. Tilings Encyclopedia AKN](https://tilings.math.uni-bielefeld.de/)).

That the **triacontahedron is the shadow of the 6-cube** is the cleanest possible statement of "the 3-D
icosahedral occupation domain is a projection of the 6-D unit cell" — a zonohedron is by definition a 3-D
projection of a hypercube, and the 6-cube (hexeract) projects into a rhombic-triacontahedron envelope.
([Zonohedron — Wikipedia](https://en.wikipedia.org/wiki/Zonohedron);
[Rhombic Triacontahedron — Wolfram MathWorld](https://mathworld.wolfram.com/RhombicTriacontahedron.html);
fig. "rhombic triacontahedron obtained as part of the projection of 6D cube" in
[Koca et al., ResearchGate](https://www.researchgate.net/figure/The-rhombic-triacontahedron-obtained-as-part-of-the-projection-of-6D-cube_fig7_279978070).)
(The triacontahedron is in fact one
of exactly **five golden isozonohedra**: the prolate & oblate rhombohedra, the rhombic dodecahedron-of-
second-kind (Bilinski), the rhombic icosahedron, and the triacontahedron — the building blocks of the
whole story.)

**PROVEN (Kramer–Neri 1984; rigour by Hof 1995 / Schlottmann 2000):** the resulting point set is a
**regular model set** (window boundary has measure zero), hence has **pure-point diffraction** — sharp
Bragg peaks indexed by 6 integers. This is the icosahedral instance of the model-set diffraction theorem
in broad doc 02 §6. ([Kramer & Neri, *On periodic and nonperiodic space fillings of Eᵐ obtained by
projection*, Acta Cryst. A 40 (1984) 580](https://doi.org/10.1107/S0567739484001495); pure-pointness:
broad doc 02 §6.)

---

## 3. The 3D Penrose / rhombohedral tiling — the 2-tile analogue (Ammann–Kramer–Neri)

### 3.1 History and the two tiles

The **Ammann–Kramer–Neri (AKN) tiling** — universally called the **3-dimensional Penrose tiling** — was
**found by Robert Ammann**, introduced by **A. L. Mackay (1981)**, and given its theoretical
cut-and-project description by **P. Kramer & R. Neri (1984)**, published essentially simultaneously with
Shechtman's experiment. ([Frettlöh, *ABCK tilings*, §1](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf);
[Tilings Encyclopedia / Bielefeld](https://tilings.math.uni-bielefeld.de/): "The Ammann–Kramer tiling …
sometimes called the 3-dimensional Penrose tiling because it generalizes Penrose's 2-dimensional
tilings … used to describe icosahedral quasicrystals.")

It uses **two prototiles — both golden rhombohedra** (parallelepipeds whose 6 faces are all the same
golden rhombus, face diagonal ratio `τ`):

- **Prolate (acute) rhombohedron** `A` — the "tall/pointy" one.
- **Oblate (obtuse) rhombohedron** `O` — the "squashed" one.

**Ten prolate + ten oblate assemble into the rhombic triacontahedron** (Kowalewski 1935) — the same
triacontahedron that is the CPS window, which is no coincidence: the window IS the central cluster.
([Frettlöh §1](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf): "Ten obtuse and ten acute
prototiles can be assembled into a triacontahedron; this was noted already in 1935 by G. Kowalewski.")

### 3.2 Volumes, frequencies, and the **τ³ inflation**

- **Volume ratio** prolate:oblate `= τ : 1`; the prolate occurs `τ` times as often as the oblate. So
  long-range, `#prolate / #oblate = τ`. (This is the 3-D echo of the planar Penrose `fat:thin = τ`.)
- **Inflation factor = `τ³`.** An inflation rule for the two rhombohedra was derived by **Audier & Guyot
  (1988)**; the linear scale factor is **`τ³ ≈ 4.236`**, i.e. each rhombohedron subdivides into smaller
  rhombohedra of `1/τ³` the linear size. Frettlöh notes this large factor explicitly: *"the inflation
  factor is pretty large, namely, `τ³`"* — and cites it as a reason the ABCK (factor `τ`) description is
  often preferred. ([Frettlöh §1](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf);
  [Audier & Guyot, *A perfect icosahedral atomic structure*, Phil. Mag. Lett. 58 (1988) 17](https://doi.org/10.1080/09500838808214724);
  illustrative inflation in [Lord–Ranganathan–Kulkarni, *Tilings, coverings, clusters and quasicrystals*, Current Sci. 78 (2000) 64](https://www.currentscience.ac.in/Volumes/78/01/0064.pdf)).

> **`τ³` is the 3-D Pisot scale factor** — the eigenvalue audit's Perron value (§2.2, §4). `τ³` is a
> Pisot number (its conjugate `σ³ = (−1/τ)³ ≈ −0.236` has modulus `< 1`), and Pisot-ness ↔ pure-point
> order is the bridge between our projection chart and substitution chart (broad doc 03).

---

## 4. Danzer's ABCK tetrahedra — the 4-tile set (the cleanest substitution chart in 3D)

The **second family** (face-centred / `D₆`-based) is by **L. Danzer (1989)** and the equivalent
**Socolar–Steinhardt (1986)** tiling. Danzer's set — the **ABCK tilings** — is the 3-D analogue with the
**simplest inflation (factor `τ`, not `τ³`)** and is the best-documented; it is our preferred substitution
chart in 3D. Primary source: [Frettlöh, *ABCK tilings*](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf)
and [Danzer, *Three-dimensional analogs of the planar Penrose tilings and quasicrystals*, Discrete Math. 76 (1989) 1](https://doi.org/10.1016/0012-365X(89)90282-3).

### 4.1 The four tiles A, B, C, K (PRECISE)

Start from the **root system `ΔH₃`** of the icosahedral group; take all tetrahedra whose **faces are
parallel to the mirror planes of the icosahedron** (face normals in `ΔH₃`). There are exactly **15
similarity classes** A,…,P; all dihedral angles are multiples of `π/2, π/3, π/5`. Halving/thirding
dihedral angles dissects each into smaller members of the family; **a closed set of just four classes —
A, B, C, K — suffices**. Exact vertex coordinates (Frettlöh, Table 1; `τ = (1+√5)/2`):

| Tile | vertex 1 | vertex 2 | vertex 3 | vertex 4 |
|---|---|---|---|---|
| **A** | `(0,0,0)` | `(τ³,0,τ²)` | `(τ²,τ²,τ²)` | `(τ²,1,0)` |
| **B** | `(0,0,0)` | `(τ³,0,τ²)` | `(τ²,τ²,τ²)` | `(τ²,τ,1)` |
| **C** | `(0,0,0)` | `(−τ,0,1)` | `(τ²,τ²,τ²)` | `(0,τ²,1)` |
| **K** | `(0,0,0)` | `(−1,τ,0)` | `(τ,τ,τ)` | `½(−1, 1/τ, τ)` |

- The four tetrahedra have **edge lengths built from `1` and `τ`**; their **faces are Robinson
  triangles** (the same `36–72–72` / `36–36–108` golden triangles whose pairing gives the planar Penrose
  rhombi) — so **ABCK is the literal 3-D lift of the Penrose-Robinson triangle tiling**. ([Frettlöh §1.1;
  search consensus.](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf))
- `A, B, C` each have exactly **one** "blue" (π/2-dihedral) edge; `K` has **three** mutually orthogonal
  ones at vertex 4 (whose coordinates are *half*-integers — the one exception to lattice-integrality).
- **`K` is the fundamental region of the icosahedral group**: the group orbit of `K` (`60K + 60K̄`,
  i.e. `30·(2K+2K̄)`) **generates the rhombic triacontahedron** — tying ABCK back to the same window.
  ([Al-Siyabi–Koca–Koca 2020](https://arxiv.org/abs/2003.13449): "The tetrahedron K constitutes the
  fundamental region of the icosahedral group and generates the rhombic triacontahedron upon the group
  action.")

### 4.2 The inflation matrix and its eigenvalues — the 3D eigenvalue audit (PROVEN)

Each tile dissects into copies congruent to `τ⁻¹A, τ⁻¹B, τ⁻¹C, τ⁻¹K`, so the inflation multiplier is
**`τ`** (linear). The **substitution matrix** (counts of A,B,C,K in the inflation of each) is
([Frettlöh §1.1](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf); also
[Baake–Grimm, *Aperiodic Order* Vol. 1, CUP 2013, p. 231](https://www.cambridge.org/core/books/aperiodic-order/)):

```
            ⌈ 0  0  1  0 ⌉
 M_ABCK  =  | 3  2  0  1 |          (columns/rows ordered A, B, C, K)
            | 2  1  2  0 |
            ⌊ 6  4  2  1 ⌋
```

**Eigenvalues (the audit):**

| eigenvalue | value | role |
|---|---|---|
| `λ_PF = τ³` | `≈ 4.236` | **Perron–Frobenius** — the volume inflation (linear `τ`, volume `τ³`) |
| `τ` | `≈ 1.618` | expanding-ish conjugate |
| `−τ⁻¹` | `≈ −0.618` | **contracting** |
| `−τ⁻³` | `≈ −0.236` | **contracting** |

> The PF eigenvalue is `τ³` **"as it ought to be, since the inflation multiplier is τ"** (volume scales
> as the cube). Two eigenvalues contract — this is the **trace budget / Galois-conjugate contraction**
> that powers pure-pointness, exactly as in `M_ABCK`'s relation to the `E⊥` block of §2.2. The normed PF
> eigenvector gives the **prototile frequencies**: `(A,B,C,K) ≈ (0.0379, 0.2829, 0.1604, 0.5189)` — i.e.
> *more than half of all tiles are `K`, and `A` is rare* ([Frettlöh §1.1](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf)).

### 4.3 Matching rules, MLD relations, and pure-pointness (PROVEN)

- **Local matching rules (purely geometric).** (i) tiles meet face-to-face; (ii) across any face
  containing a "blue" (π/2) edge, the neighbour is the **mirror image**. Equivalently, group the tiles
  into four **octahedra** `⟨A⟩,⟨B⟩,⟨C⟩,⟨K⟩` (the blue edges then vanish): *all* face-to-face tilings by
  these four octahedra are ABCK tilings — a clean geometric local rule. ABCK also admits an **Ammann-
  planes** decoration (3-D analogue of Ammann bars). ([Frettlöh §1.2; Stehling, *Ammann bars and
  quasicrystals*, DCG 7 (1992) 125](https://doi.org/10.1007/BF02187829)).
- **MLD web.** ABCK is **mutually locally derivable (MLD)** with the **Socolar–Steinhardt** zonohedral
  tiling (4 zonohedra: rhombic hexahedron, rhombic dodecahedron, rhombic icosahedron, rhombic
  triacontahedron); the SS vertices are exactly ABCK's class-II and class-III vertices. ([Roth, *J. Phys.
  A* 26 (1993) 1455](https://doi.org/10.1088/0305-4470/26/6/035); [Danzer–Papadopolos–Talis, *Int. J. Mod.
  Phys. B* 7 (1993) 1379](https://doi.org/10.1142/S0217979293002389)).
- **PROVEN pure-point (Kramer–Papadopolos–Schlottmann–Zeidler 1994).** The `⟨ABCK⟩` (octahedral)
  vertices form **model sets with internal space ℝ³ and lattice `D₆`**; hence **both `⟨ABCK⟩` and ABCK
  are pure-point diffractive** (Frettlöh Thm 1.3–1.4). ([Kramer–Papadopolos–Schlottmann–Zeidler,
  *Projection of the Danzer tiling*, J. Phys. A 27 (1994) 4505](https://doi.org/10.1088/0305-4470/27/13/027)).

---

## 5. The window / occupation-domain structure in 3D (the geometry that does the work)

This is the heart for us: **in 3D the windows are 3-D polytopes in `E⊥`, and the *shape* of each window
is the structure.** For the `D₆`/ABCK CPS there are **three vertex classes I, II, III**, each its **own
model set with its own window** in `E⊥ = ℝ³` (a fourth class IV — the eight-`K` vertex — cannot be
projected consistently). The windows (Frettlöh §1.3, after Kramer–Papadopolos–Schlottmann–Zeidler 1994):

| Vertex class | Window in `E⊥` | "Long-edge" length | Window volume |
|---|---|---|---|
| **I** | dodecahedron with 5-fold stars *engraved* on each face (no standard name) | `4τ/√(τ+2)` | `20(5τ+2)` |
| **II** | regular **dodecahedron**, edge 2 | `2` | `4(7τ+4)` |
| **III** | **great dodecahedron** (a Kepler–Poinsot star polyhedron) | `2τ` | `20τ²` |

These arise from the **three classes of holes of `D₆`** (deep + two shallow); the projection is just
"omit the last three coordinates." **Window volume = point frequency**: `d_x = vol(W_x)/det(D₆)`, with
`det(D₆) = 16(τ+2)³`, giving densities `d_I ≈ 0.2663`, `d_II = τ/20 ≈ 0.0809`, `d_III ≈ 0.0691`. The
whole vertex set is one model set with **internal space `ℝ³ × ℂ₄`** (the `ℂ₄` factor enumerates the
vertex classes, exactly as Penrose's CPS uses `ℝ² × ℂ₅`). ([Frettlöh §1.3, Thm 1.3](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf)).

The dual/physics view: **occupation domains are 3-D polytopes** (triacontahedra and their relatives) and
the physical structure is `OD ∩ E∥` at the irrational cut; diffraction intensities are the **Fourier
transform of the OD evaluated at the perp wavevector `G⊥`** (broad doc 04 §3.3, §5; [Steurer 2018, Acta
Cryst. A74, 1 — PMC mirror](https://pmc.ncbi.nlm.nih.gov/articles/PMC5740452/);
[Katz & Gratias / Katz, *Some local properties of the 3-dim. Penrose tilings*, in *Introduction to the
Mathematics of Quasicrystals* (Jarić ed., 1989)](https://www.sciencedirect.com/book/9780120406029)).

> **Takeaway.** The 3-D windows are **polytopes** (dodecahedron, great dodecahedron, triacontahedron) —
> *measure-zero (flat) boundaries*. Polytopal windows give **finite, ≥2-element protosets** (2
> rhombohedra, or 4 ABCK tetrahedra). The single-tile knob (§6) is exactly to leave the polytopal regime.

---

## 6. ★ The single-prototile-collapse question — can a *fractal-window reprojection* yield a 3D monotile?

This is the load-bearing section for the project. Restate the planar mechanism (broad doc 02 §7–8),
then ask the 3-D analogue precisely.

### 6.1 Why the planar hat is ONE tile: the fractal Rauzy window

- A **polytopal canonical window** partitions `E⊥` into finitely many cells by "which neighbours are
  co-accepted"; **each cell ↦ one prototile**. Polytope ⇒ small but **≥2-tile** protoset (Penrose 2,
  Ammann–Beenker 2). ([*Canonical projection tilings defined by patterns*, arXiv:1812.06863](https://arxiv.org/pdf/1812.06863); broad doc 02 §7.)
- The **hat/spectre** are **MLD with reprojections of regular model sets whose windows are *Rauzy
  fractals*** — windows with **non-integer Hausdorff-dimension boundary** that are nonetheless *regular*
  (measure-zero boundary), so pure-point order survives. **The minimal CPS is physical `ℝ²` × internal
  `ℝ²` = `ℝ⁴`** (an earlier Socolar-style embedding "used two unnecessary dimensions," i.e. 6-D). **It is
  precisely the *fractality* of the window that collapses the 2-tile protoset to a *single* tile.**
  ([Baake–Gähler–Mazáč–Mitchell, *Diffraction of the Hat and Spectre tilings…*, arXiv:2502.03268](https://arxiv.org/abs/2502.03268);
  [Baake–Gähler–Mazáč–Sadun, *On the long-range order of the Spectre tilings*, arXiv:2411.15503](https://arxiv.org/abs/2411.15503),
  publ. *Discrete Comput. Geom.* (2025); broad doc 02 §8.)

> **The collapse recipe, abstracted:** *take a regular model set in a minimal CPS; deform/reproject its
> window to a regular **fractal** (Rauzy-type) window; the fractal boundary merges the polytope's
> several acceptance cells into one orbit ⇒ a single prototile, while measure-zero boundary keeps
> diffraction pure-point.* The hat is the existence proof that this can happen.

### 6.2 The 3-D analogue — stated precisely, and what is PROVEN vs OPEN

The 3-D icosahedral CPS is **physical `ℝ³` × internal `ℝ³` = `ℝ⁶`**, with **polytopal** windows
(triacontahedron; dodecahedron / great dodecahedron) giving **2 rhombohedra** or **4 ABCK tetrahedra**.
The exact analogue of the hat question is:

> **Q (the 3-D collapse question).** Is there a **regular *fractal* window** in the internal `ℝ³` (a 3-D
> Rauzy-type domain), for the `ℤ⁶`/`D₆` icosahedral lattice (or a reprojection of it), whose model set is
> **MLD with a tiling by a SINGLE prototile** — and is that tile then **strongly aperiodic**?

Status of the surrounding facts:

- **PROVEN (Schmitt 1988; Conway+Danzer convex extension; reaffirmed Kaplan, arXiv:2509.12216, 2 Sep
  2025).** A single 3-D tile that admits **only non-periodic** tilings *exists* — the **Schmitt–Conway–
  Danzer (SCD) biprism**, a **convex** polyhedron (topologically a gyrobifastigium, with parallelogram +
  irregular-triangle faces). **BUT it is only *weakly* aperiodic**: its tilings admit a **screw symmetry**
  (rotation by an irrational multiple of `π` composed with an axial translation) — an infinite cyclic
  symmetry group, just no pure translation. ([Einstein problem — Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem):
  "no tiling by this prototile admits a translation as a symmetry, some have a screw symmetry"; Schmitt
  1988, Conway & Danzer convex version; [Kaplan, *The Path to Aperiodic Monotiles*, arXiv:2509.12216](https://arxiv.org/abs/2509.12216),
  §"Aperiodicity": SCD "tiles space without ever permitting translational symmetries, but … admits
  tilings that contain a screw motion … which can be repeated any number of times.")
- **OPEN (as of June 2026).** A **strongly aperiodic 3-D monotile** — one admitting **no infinite cyclic
  group of Euclidean motions** (Goodman-Strauss's strong definition; no screw either) — **is not known**.
  Kaplan (Sep 2025) frames the SCD screw as the open gap and writes that adapting the hat methods to 3D
  is feasible in principle but "I am daunted by the prospect of deducing the behaviour of any candidate
  shapes that might be discovered there." This is the headline open target our 3D strategy aims at.
  ([Kaplan, arXiv:2509.12216, §"Aperiodicity"](https://arxiv.org/abs/2509.12216); broad-round README item
  5 lists "3D / higher dimensions — strongly-aperiodic" as a top frontier.)
- **OPEN / UNVERIFIED claim worth a flag (Taillefer 2025).** A non-peer-reviewed preprint —
  **C. S. Taillefer, *Rigorous Construction of a Countably Infinite Family of Fractal-Boundary Aperiodic
  Monotiles in 𝔼³*** (Academia.edu, 2025; **no arXiv ID; not peer-reviewed**) — claims a countable family
  `{Mₙ}` of **single, strongly-aperiodic 3-D monotiles** built by **decorating a rhombic triacontahedron
  with fractal "antennas"** (a boundary-deformation operator encoding a substitution), with **purely
  singular-continuous** diffraction. **This is exactly our motif** (triacontahedron + fractal boundary as
  a physical substitution encoding), and if correct it would *settle* the strong 3-D monotile question —
  but its base tile is the triacontahedron with hierarchical fractal locking, **not** a clean fractal-
  window CPS, and the construction is **unverified**. Treat as a *lead to scrutinise*, not a result.
  ([Taillefer 2025, Academia.edu](https://www.academia.edu/130358073/);
  cross-check vs the rigorous fractal-window CPS line below.)
- **PROVEN that the fractal-window route is "model-set-legal" in principle.** The hat result establishes
  that **regular fractal windows exist and give pure-point monotile shadows in `ℝ²`**. There is, to our
  knowledge, **no published 3-D icosahedral fractal-window construction collapsing to one tile** — so the
  3-D collapse question is **genuinely OPEN and on-strategy**. (Related rigorous direction: [Baake et al.,
  *Diffraction of the Hat and Spectre…*, arXiv:2502.03268](https://arxiv.org/abs/2502.03268), and the
  general fractal-window/Rauzy machinery; no icosahedral analogue published as of 2026-06.)

### 6.3 Honest assessment of feasibility (the realistic verdict)

- **The two charts already exist in 3D and are clean.** Projection chart: `ℤ⁶`/`D₆` icosahedral CPS with
  triacontahedral window (§2). Substitution chart: ABCK with matrix `M_ABCK`, Perron `τ³`, contracting
  conjugates (§4). Their gluing Pisot number `τ³` is in hand. So the *infrastructure* for a 3-D
  shadow-design is fully built and citable.
- **The collapse to ONE tile is the unproven step.** In the plane it required a *fractal* window plus a
  *minimal* (ℝ⁴) embedding and an MLD argument — none of which is automatic. In 3D the embedding is
  `ℝ⁶` (icosahedral) and the windows are polytopes; **a 3-D Rauzy/fractal reprojection collapsing 2
  rhombohedra (or 4 ABCK) to one tile has not been exhibited**, and there is **no theorem guaranteeing it
  exists** (nor one forbidding it). The strong-aperiodicity requirement (no screw) is an *extra* hurdle
  SCD shows is real in 3D and that the model-set/pure-point route would *automatically clear* (model sets
  have trivial point symmetry generically — no screw axis), which is a genuine *advantage* of the shadow
  approach over ad-hoc convex tiles.
- **Net.** A strongly-aperiodic 3-D monotile realised as a **fractal-windowed reprojection of the
  icosahedral model set** is **(a) not ruled out, (b) directly analogous to the proven planar hat
  mechanism, and (c) the single most on-strategy 3-D target**. It is open as of 2026-06.

---

## 7. Other 3D aperiodic structures (axial; small-protoset notes)

- **Decagonal / dodecagonal / octagonal = AXIAL quasicrystals.** These are **quasiperiodic in a plane
  and *periodic* along the unique axis** — i.e. a **periodic stacking of a 2-D quasicrystal**. Embedding
  is **5-D** (decagonal, dodecagonal: 4 perp-plane + 1 periodic) or **4-D** (octagonal). They are *not*
  fully 3-D-aperiodic, so they are **weaker** higher-layer targets for a genuinely-3D monotile, though
  excellent for "2D-quasiperiodic × periodic" hybrids. Decagonal QC = "oblique projection of the 5-D unit
  cell … its shadow from hyperspace"; dodecagonal = periodic `ABA̅B` stacking of a 12-fold layer.
  ([Decagonal Quasicrystal — ScienceDirect overview](https://www.sciencedirect.com/topics/chemistry/decagonal-quasicrystal);
  [Quasicrystal — Wikipedia](https://en.wikipedia.org/wiki/Quasicrystal); real materials Al–Ni–Co,
  Al–Cu–Co — broad doc 04 §6.)
- **Small-protoset 3-D aperiodic sets — the current census.**
  - **2 tiles:** AKN golden rhombohedra (§3). The smallest *genuinely-3D* aperiodic protoset by tile
    count, but they need matching rules / the projection to force aperiodicity.
  - **4 tiles:** Danzer ABCK tetrahedra (§4) — with the simplest local geometric rule.
  - **1 tile, weakly aperiodic:** SCD biprism (convex, but screw symmetry) — §6.2.
  - **1 tile, strongly aperiodic:** **none proven** (§6.2). The open prize.
- **Mosseri–Sadoc / curved-space and `4D→3D` exotica** exist (e.g. mapping icosahedral order to the
  3-sphere `{3,3,5}` polytope) but are tangential to a Euclidean monotile. (Mentioned for completeness;
  see [Sadoc–Mosseri, *Geometrical Frustration*, CUP 1999](https://www.cambridge.org/9780521031875).)

---

## 8. The pervasive role of `τ` and `τ³`

- **`τ` everywhere in the geometry:** golden-rhombus faces (diagonal ratio `τ`); rhombohedron volume
  ratio `τ:1`; tile-frequency ratios in `τ`; ABCK edges from `{1, τ}`; the icosahedral star
  `(1,τ,0),…`; the window volumes `20(5τ+2), 4(7τ+4), 20τ²`; `det(D₆)=16(τ+2)³`.
- **`τ³` as the 3-D *scale* factor:** the AKN rhombohedral inflation (Audier–Guyot) and the **Perron
  eigenvalue of `M_ABCK`** are both **`τ³`** (linear factor `τ`, *volume* factor `τ³`). `τ³` is a **Pisot
  number** (conjugate `|σ³|≈0.236<1`), so the substitution is pure-point — the Pisot↔diffraction bridge
  of broad doc 03. The contracting conjugate eigenvalues `−τ⁻¹, −τ⁻³` are the **trace budget / internal-
  space contraction** that the projection chart sees as the `σ`-block of the Coxeter polynomial (§2.2,
  §4.2). **`τ³` is our 3-D `λ`.**

---

## 9. Authoritative sources (titles + URLs)

**Primary — the 3D tilings, tiles, inflation, CPS**
- D. Frettlöh, *Icosahedral tilings in ℝ³: the ABCK tilings* (lecture notes; Tilings-Encyclopedia author)
  — https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf  **[main source: vertex coords,
  `M_ABCK`, eigenvalues, windows, MLD]**
- L. Danzer, *Three-dimensional analogs of the planar Penrose tilings and quasicrystals*, Discrete Math.
  76 (1989) 1–7 — https://doi.org/10.1016/0012-365X(89)90282-3
- P. Kramer & R. Neri, *On periodic and nonperiodic space fillings of Eᵐ obtained by projection*, Acta
  Cryst. A 40 (1984) 580 (erratum A41 (1985) 619) — https://doi.org/10.1107/S0567739484001495
- P. Kramer, Z. Papadopolos, M. Schlottmann, D. Zeidler, *Projection of the Danzer tiling*, J. Phys. A 27
  (1994) 4505 — https://doi.org/10.1088/0305-4470/27/13/027  **[model-set proof, the three windows]**
- A. Al-Siyabi, N. O. Koca, M. Koca, *Icosahedral Polyhedra from D₆ lattice and Danzer's ABCK Tiling*,
  Symmetry 12 (2020) 1983 — https://arxiv.org/abs/2003.13449 (https://www.mdpi.com/2073-8994/12/12/1983)
  **[D₆→3D projection, H₃ generators, Coxeter-poly factorisation, K↦triacontahedron]**
- J. E. S. Socolar & P. J. Steinhardt, *Quasicrystals II: Unit-cell configurations*, Phys. Rev. B 34
  (1986) 617 — https://doi.org/10.1103/PhysRevB.34.617
- M. Audier & P. Guyot, *A perfect icosahedral atomic structure: two-unit-cell and four-zonohedra
  description*, Phil. Mag. Lett. 58 (1988) 17 — https://doi.org/10.1080/09500838808214724  **[τ³ inflation]**
- M. Baake, D. Joseph, P. Kramer, M. Schlottmann, *Root lattices and quasicrystals*, J. Phys. A 23 (1990)
  L1037 — https://doi.org/10.1088/0305-4470/23/19/008  **[P/F/B-type from `ℤ⁶`/`D₆`/`D₆*`]**

**Windows / occupation domains / geometry**
- *Rhombic triacontahedron* — Wikipedia — https://en.wikipedia.org/wiki/Rhombic_triacontahedron
  (golden-rhombus faces; 10+10 golden-rhombohedron dissection)
- A. Katz, *Some local properties of the 3-dim. Penrose tilings*, in *Introduction to the Mathematics of
  Quasicrystals* (M. V. Jarić, ed.), Academic Press 1989 — https://www.sciencedirect.com/book/9780120406029
- W. Steurer, *Quasicrystals: What do we know? …*, Acta Cryst. A74 (2018) 1 — https://pmc.ncbi.nlm.nih.gov/articles/PMC5740452/
- W. Steurer & S. Deloudi, *Crystallography of Quasicrystals*, Springer 2009 (ch. "Higher-Dimensional
  Approach") — https://link.springer.com/chapter/10.1007/978-3-642-01899-2_3

**The 3D monotile status / single-tile question**
- C. S. Kaplan, *The Path to Aperiodic Monotiles*, arXiv:2509.12216 (2 Sep 2025) —
  https://arxiv.org/abs/2509.12216  **[authoritative current status: SCD weak, strong 3D OPEN]**
- *Einstein problem* — Wikipedia — https://en.wikipedia.org/wiki/Einstein_problem  **[SCD history, screw,
  strong vs weak]**
- M. Baake, F. Gähler, J. Mazáč, A. Mitchell, *Diffraction of the Hat and Spectre tilings and some of
  their relatives*, arXiv:2502.03268 (2025) — https://arxiv.org/abs/2502.03268  **[fractal-window CPS, the
  collapse mechanism we extend]**
- M. Baake, F. Gähler, J. Mazáč, L. Sadun, *On the long-range order of the Spectre tilings*,
  arXiv:2411.15503 (2024/25), *Discrete Comput. Geom.* — https://arxiv.org/abs/2411.15503
- C. S. Taillefer, *Rigorous Construction of a Countably Infinite Family of Fractal-Boundary Aperiodic
  Monotiles in 𝔼³*, Academia.edu (2025), **unrefereed preprint** — https://www.academia.edu/130358073/
  **[UNVERIFIED claim of a strongly-aperiodic 3D monotile via triacontahedron + fractal antennas — flag,
  do not rely on]**

**Foundational references / textbooks**
- M. Senechal, *Quasicrystals and Geometry*, CUP 1995 — https://www.cambridge.org/9780521575416
- M. Baake & U. Grimm, *Aperiodic Order, Vol. 1: A Mathematical Invitation*, CUP 2013 (ABCK at p. 231) —
  https://www.cambridge.org/core/books/aperiodic-order/
- Tilings Encyclopedia (Frettlöh–Gähler–Harriss), Bielefeld — https://tilings.math.uni-bielefeld.de/

---

## Relevance to our shadow / strict-extension approach

**What the 3D "higher layer" concretely is.** It is the **6-D periodic lattice `ℤ⁶` (primitive) or `D₆`
(face-centred)** carrying a faithful **icosahedral `H₃`** action, split as **physical `E∥ = ℝ³` ⊕
internal `E⊥ = ℝ³`**, the two ℝ³'s being **exchanged by the Galois conjugation `τ ↔ σ = −1/τ`**. The
*shadow* downstairs is the icosahedral quasicrystal; the *audit* is that the `D₆` Coxeter polynomial
**factors** into an expanding `τ`-block (physical) and a contracting `σ`-block (internal) — our
eigenvalue/trace-budget audit, made literal as a polynomial factorisation (§2.2). The internal `E⊥` is
the **3-D contracting Galois-conjugate space where the window lives** — the exact 3-D home of the
Rauzy-type window. Both charts are already built and citable:

- **Projection chart (T-shadow):** `ℤ⁶`/`D₆` CPS, **triacontahedral window** (= projection of the
  6-cube; = the central 10-prolate-+-10-oblate cluster). Regular model set ⇒ **pure-point** (PROVEN:
  Kramer–Neri 1984; Kramer–Papadopolos–Schlottmann–Zeidler 1994).
- **Substitution chart (T2/stacking):** **ABCK** with matrix `M_ABCK`, **Perron `λ = τ³`**, contracting
  conjugates `−τ⁻¹, −τ⁻³` — i.e. **`τ³` is our 3-D Pisot inflation `λ`**, and recognizability/
  pure-point order is the matrix's contraction budget (PROVEN pure-point).

**The strict-extension certificate in 3D.** Aperiodicity = the cut is irrational (no `ℤ⁶` vector lies in
`E∥`) = the substitution is recognizable/non-factorizing; the contraction of `−τ⁻¹, −τ⁻³` (equivalently
the `σ`-block) is the certificate's spectral side. A genuine bonus of the shadow route in 3D: model sets
have **no screw symmetry** generically, so a model-set monotile would be **strongly** aperiodic *by
construction* — directly clearing the very gap (SCD's screw) that keeps the strong-3D-monotile problem
OPEN.

**The most promising (lattice, window) starting points for collapsing toward one tile.** The planar hat
proves the collapse recipe — *minimal CPS + **regular fractal (Rauzy) window** merges a polytope's
acceptance cells into one prototile orbit*. Ranked 3-D leads:

1. **`D₆` icosahedral CPS + a 3-D Rauzy/fractal reprojection of the `⟨ABCK⟩` model set.** Start from the
   *proven* `D₆` model set (3 polytopal windows: engraved-dodecahedron, dodecahedron, great
   dodecahedron) and seek a **fractal redrawing of these windows** (regular, measure-zero boundary) that
   merges the **4 ABCK tetrahedra → 1** prototile. This is the literal 3-D port of Baake–Gähler–Mazáč's
   hat construction. **Best-defined target.**
2. **`ℤ⁶` icosahedral CPS + fractal triacontahedral window collapsing the 2 rhombohedra → 1.** Fewer
   starting tiles (2 not 4), but inflation is the larger `τ³`; deform the triacontahedral window to a
   regular fractal so the *prolate/oblate* acceptance cells fuse. The triacontahedron is also exactly the
   object Taillefer (unverified) decorates with fractal antennas — so this is the lattice/window pair to
   scrutinise first, *with* the rigorous CPS machinery the Taillefer preprint lacks.
3. **Minimal-dimension reprojection.** The hat's key trick was dropping from a 6-D Socolar embedding to a
   **minimal ℝ⁴**. Ask whether the icosahedral shadow has a **lower-than-6 reprojection** (it should
   not, by the rank-6 icosahedral module — *verify*), or whether a chosen *sub-symmetry* (e.g. a single
   5-fold axis) admits a smaller minimal CPS whose fractal window gives one tile. Investigate before
   committing.

**Audit checklist for any 3-D candidate (λ, W):** (i) **λ Pisot/Perron** — `τ³` qualifies (PROVEN);
(ii) **W regular** (measure-zero, even if fractal) ⇒ pure-point (Hof–Schlottmann); (iii) **single
acceptance-orbit** ⇒ monotile (the fractal-window collapse, to be exhibited); (iv) **no screw**, which a
generic model set gives for free ⇒ *strong* aperiodicity. Items (i)–(ii) are in hand; **(iii) is the
open, on-strategy step**, and (iv) is the payoff that makes the 3-D shadow route preferable to convex
(SCD-style) tiles.

> **Bottom line.** A strongly-aperiodic 3-D monotile is **OPEN (2026-06)**; SCD only gives *weak*
> (screw). The 3-D higher layer (`ℤ⁶`/`D₆`, icosahedral, triacontahedral window, `λ = τ³`) is fully
> built and pure-point-proven. The *one* unproven move — exactly mirroring the planar hat — is a
> **regular fractal-window reprojection that collapses the icosahedral protoset (2 rhombohedra or 4 ABCK
> tetrahedra) to a single prototile**. That is the concrete 3-D target.
