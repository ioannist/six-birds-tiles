# 02 — Cut-and-Project Sets, Model Sets, and the Projection (Shadow) Formalism

> Research pillar for *six-birds-tiles*. This is the load-bearing mathematical layer: it is the
> rigorous, century-old theory that says an aperiodic tiling **is** the down-projection (shadow) of a
> periodic lattice in a higher-dimensional space, cut at an **irrational** orientation. Everything in
> [`docs/APPROACH.md`](../docs/APPROACH.md) — "tile = shadow of a higher layer," "the work is
> upstairs," "irrational direction as the non-descending object" — is the *projection chart* of this
> theory, stated in standard quasicrystal / aperiodic-order language. See the final section for the
> exact dictionary.

---

## 1. Overview

There are two dominant mathematical sources of aperiodic order: **primitive substitutions** (inflation
rules) and **cut-and-project schemes**, whose outputs are called **model sets**
([Baake–Grimm–Richard–Strungaru survey, arXiv:0802.3242](https://arxiv.org/pdf/0802.3242)). The
projection method was introduced for Penrose-type tilings by **N. G. de Bruijn (1981)**, who showed
that Penrose rhombus tilings are 2-D slices/projections of a periodic lattice in 5-dimensional space —
the historical starting point of the theory
([Tilings Encyclopedia, "Cut and Project"](https://tilings.math.uni-bielefeld.de/glossary/cut-and-project/)).

The single governing idea, stated crisply:

> "Obtain an aperiodic structure as a suitable **slice** of a higher-dimensional periodic lattice,
> which is then **projected** onto a space of the desired dimension."
> — [*Mathematical diffraction of aperiodic structures*, arXiv:1205.3633](https://arxiv.org/pdf/1205.3633)

If the slicing/projection direction is **rational** with respect to the lattice, the shadow is
**periodic** (it is just a lattice plane). If the direction is **irrational/incommensurate**, the
shadow is **aperiodic** yet retains long-range order, because the order is inherited from the periodic
parent upstairs. This is the entire mechanism, and it is exactly the shadow philosophy of this project.

A landmark structural fact closes the loop with diffraction: **regular model sets have pure-point
diffraction** (Hof 1995 for Euclidean internal spaces; Schlottmann 2000 in full generality). That is
the mathematical signature of a quasicrystal — sharp Bragg peaks without periodicity — and it is the
"long-range order" certificate that a genuine higher-layer shadow must exhibit.

---

## 2. The cut-and-project scheme — precise definitions

### 2.1 The scheme (CPS)

A **cut-and-project scheme (CPS)** is the data
([Baake–Grimm survey, arXiv:0802.3242](https://arxiv.org/pdf/0802.3242);
[Moody, *Model Sets: A Survey*, arXiv:math/0002020](https://arxiv.org/pdf/math/0002020)):

```
            π                          π_int
   ℝ^d  <──────  ℝ^d × H  ──────────────────────────>  H
 (physical          ↑                              (internal /
  E∥, "direct"      │ L  (lattice, full rank)       perpendicular
  space, dim d)     │                                 space E⊥)
                  𝓛 = π(L)   ⊂ ℝ^d           𝓛* = π_int(L) dense ⊂ H
```

Concretely, the ingredients are:

- **Physical (direct, parallel) space `E∥ = ℝ^d`** — where the tiling/point set lives (for planar
  tilings `d = 2`).
- **Internal (perpendicular) space `H`** — a locally compact abelian group; in the Euclidean case
  `H = ℝ^m`. Often written `E⊥`.
- **A lattice `L ⊂ ℝ^d × H`** — a co-compact discrete subgroup of the total space (the
  higher-dimensional periodic parent). In the canonical Euclidean case the total space is
  `ℝ^n = ℝ^d ⊕ ℝ^m` with `n = d + m`, and `L = ℤ^n` (or a sublattice/root lattice) after a suitable
  rotation.
- **Two projections** `π : ℝ^d × H → ℝ^d` (to physical space) and `π_int : ℝ^d × H → H` (to internal
  space).

subject to **two standing conditions**
([labri / Sébastien Labbé, "Cut and Project Scheme"](https://www.labri.fr/perso/slabbe/docs/0.7.1/cut_and_project_scheme.html);
[Wikipedia, *Meyer set*](https://en.wikipedia.org/wiki/Meyer_set)):

1. **`π|_L` is injective** — equivalently `L ∩ ({0} × H) = {0}`. So `𝓛 := π(L)` is a bijective copy of
   `L`, and each physical point remembers a unique internal coordinate.
2. **`π_int(L)` is dense in `H`** — the internal projection fills the internal space (this forces the
   slope to be irrational; see §3).

`𝓛 = π(L)` is the (projected) point group; it is itself **not** discrete in general — it must be cut.

### 2.2 The star map (`∗`-map)

Because `π|_L` is injective, it is invertible onto `𝓛`. The **star map** is the composition that sends
a physical lattice point to its internal "shadow coordinate"
([Tilings Encyclopedia](https://tilings.math.uni-bielefeld.de/glossary/cut-and-project/);
Baake–Grimm survey):

> **`(·)* : 𝓛 → H, x ↦ x* := π_int( (π|_L)^{−1}(x) ).`**

Its graph `{ (x, x*) : x ∈ 𝓛 }` is exactly the lattice `L`. The star map is the algebraic heart of the
construction: it is a (densely defined, ℤ-linear) map carrying each physical point to the internal
space, and **the window acts on `x*`**, not on `x`. In number-theoretic examples (Fibonacci, Penrose)
the star map is **Galois conjugation** — e.g. `√5 ↦ −√5`, golden ratio `τ = (1+√5)/2 ↦ τ' = (1−√5)/2`
— which is why the irrationality is the engine.

### 2.3 The window and the model set

Fix a **window** (acceptance domain / atomic surface) `Ω = W ⊂ H`: a relatively compact set with
non-empty interior. The **cut-and-project set / model set** is
([Moody survey, arXiv:math/0002020](https://arxiv.org/pdf/math/0002020);
[Baake–Grimm survey](https://arxiv.org/pdf/0802.3242)):

> **`⋏(W)  :=  { π(x) : x ∈ L,  π_int(x) ∈ W }  =  { x ∈ 𝓛 : x* ∈ W }  ⊂  ℝ^d.`**

In words: take all lattice points of `L`, keep only those whose internal coordinate falls inside the
window `W` (the **cut**), then **project** the survivors to physical space. Equivalently, project the
slab `ℝ^d × W` of the lattice. A model set is always a **Delone set** — uniformly discrete and
relatively dense (§4) — and in fact a **Meyer set**.

A point set `Λ` is called a **model set** if there exists *some* CPS and *some* window `W` (with the
properties above) such that `Λ = t + ⋏(W)` for a translation `t`.

### 2.4 Regular and generic (non-singular) model sets

Two genericity refinements matter for diffraction
([Schlottmann 2000; Baake–Grimm survey, arXiv:0802.3242](https://arxiv.org/pdf/0802.3242)):

- **Regular model set:** the window's topological **boundary has measure zero**, `θ_H(∂W) = 0`
  (Lebesgue/Haar measure in `H`). This is the key analytic hypothesis behind pure-point diffraction.
- **Generic (non-singular) model set:** no lattice point lands on the boundary,
  `𝓛* ∩ ∂W = ∅`. Generic model sets are repetitive and form a single nice dynamical hull; singular
  ones can differ on a measure-zero set of windows.

**Canonical (cubical) window.** When `L = ℤ^n` and `W = π_int([0,1]^n)` is the internal projection of
the unit hypercube, the scheme is the **canonical projection tiling**; `W` is then a centrally
symmetric polytope (a *zonotope*) and the model set is automatically regular. Penrose and
Ammann–Beenker are of this canonical type.

---

## 3. Why rational slope ⇒ periodic and irrational slope ⇒ aperiodic

This is the conceptual crux and the literal justification for treating the irrational direction as the
project's "non-descending object."

**Rational slope ⇒ periodic.** Slicing a periodic lattice along a **rational** direction yields a
lower-dimensional cross-section that is *itself periodic* — a lattice plane, specified in
crystallography by **integer Miller indices**. Projecting it gives a crystal
([Wikipedia, *Aperiodic crystal*](https://en.wikipedia.org/wiki/Aperiodic_crystal)). Formally, a
rational slope means `E∥` contains a rank-`d` sublattice of `L`, so the projected set has a genuine
translation lattice. (In CPS terms, `π_int(L)` is then **not dense** — it is discrete — violating
condition 2 of §2.1.)

**Irrational slope ⇒ aperiodic.** If the Miller indices have **irrational ratios** — the cut is
**incommensurate** with the lattice — then:

> "the cross-section is aperiodic but still has long-range order because of the underlying
> higher-dimensional periodicity. This is what is known as the cut-and-project method."
> — [Wikipedia, *Aperiodic crystal*](https://en.wikipedia.org/wiki/Aperiodic_crystal)

The mechanism: an irrational slope forces `π_int(L)` **dense** in `H` (condition 2). Density is exactly
what makes the window cut select an aperiodic — yet repetitive and uniformly discrete — subset. A
genuine period `t ≠ 0` of the shadow would have to be a vector of `𝓛` with `t* = 0`; but injectivity of
`π|_L` (condition 1) plus density forbid a nonzero such `t`. So **no translation symmetry survives**,
while the dense internal orbit guarantees every local pattern recurs (repetitivity / Bohr almost
periodicity). The irrational direction is precisely the object that *cannot be reduced to a rational
(periodic) one* — it does not descend.

For the icosahedral case the same statement is made bluntly: "Since parallel space represents an
**irrational cut** through the hyperspace, the resulting structure cannot be periodic"
([icosahedral CPS sources, see §5.3]).

---

## 4. Model sets, Meyer sets, Delone sets — definitions and hierarchy

Definitions ([Wikipedia, *Delone set*](https://en.wikipedia.org/wiki/Delone_set);
[Wikipedia, *Meyer set*](https://en.wikipedia.org/wiki/Meyer_set);
[Moody survey](https://arxiv.org/pdf/math/0002020)):

- **Delone set** `X ⊂ ℝ^d`: both
  - **uniformly discrete** — `∃ r > 0` with `‖x − y‖ ≥ r` for distinct `x, y ∈ X`, and
  - **relatively dense** — `∃ R > 0` such that every ball of radius `R` contains a point of `X`.
  (`0 < r ≤ R < ∞`.) These are the "decent point sets" — no clumping, no gaps.

- **Meyer set** `X`: a **relatively dense** set such that the difference set `X − X` is **uniformly
  discrete**. Equivalently: `X` and `X − X` are *both* Delone. Meyer's theorem gives several equivalent
  characterizations, the decisive one being:
  > `X` is a Meyer set **iff** there exist a model set `Λ` and a **finite** set `F` with `X ⊆ Λ + F`.
  So a Meyer set is, up to a finite "decoration," a piece of a model set
  ([Wikipedia, *Meyer set*](https://en.wikipedia.org/wiki/Meyer_set)). Meyer sets were introduced by
  **Yves Meyer** in Diophantine approximation (as *harmonious sets*) a decade before quasicrystals.

- **Model set / cut-and-project set:** as in §2.3. Every model set is a Meyer set (hence Delone).

**The hierarchy** (each inclusion strict):

```
   lattices  ⊊  regular model sets  ⊊  model sets  ⊊  Meyer sets  ⊊  Delone sets  ⊊  point sets
```

- A **lattice** is the degenerate model set (trivial internal space `H = {0}`, or rational slope).
- **Regular model sets** are the "nicest" non-periodic ones — they diffract purely pointwise (§6).
- **Meyer sets** are exactly the Delone sets that sit finitely inside model sets; they are the natural
  abstract class of "quasicrystal-like" point sets (they have a relatively dense set of `ε`-dual
  vectors / Bragg directions).
- **Pure-point-diffractive Delone sets are Meyer**
  ([Lee–Solomyak / Strungaru, arXiv:math/0510389](https://arxiv.org/pdf/math/0510389);
  ["Why do Meyer sets diffract?", arXiv:2101.10513](https://arxiv.org/pdf/2101.10513)), tightening the
  link between the Meyer property and long-range order.

A useful recent sharpening: **not every Meyer set is a regular model set** — there is a clean
characterization of *which* Meyer sets are regular model sets via almost periodicity
([arXiv:2410.22536](https://arxiv.org/pdf/2410.22536)).

---

## 5. Worked examples — which famous tilings are model sets, and from what

### 5.1 Penrose tiling (the rhombic P3) — from `ℤ⁵` (or the `A₄` root lattice)

The Penrose rhombus tiling is the prototypical model set. Two standard embeddings
([Tilings Encyclopedia, Penrose Rhomb](https://tilings.math.uni-bielefeld.de/substitution/penrose-rhomb/);
[de Bruijn pentagrid sources](http://www.neverendingbooks.org/de-bruijns-pentagrids-2/);
[*Quasicrystals: Projections of 5-d Lattice*, arXiv:math-ph/0606028](https://arxiv.org/pdf/math-ph/0606028)):

| Item | Standard `ℤ⁵` scheme | Minimal `A₄` scheme |
|---|---|---|
| Total space / lattice | `ℝ⁵`, `L = ℤ⁵` | `ℝ⁴`, root lattice `A₄` (`= ℤ⁵ ∩ {Σxᵢ = 0}`) |
| Physical space `E∥` | `2`-D plane (one `D₅`-symmetric eigenplane of the cyclic shift) | `2`-D |
| Internal space `H` | `3`-D orthogonal complement of `E∥` in `ℝ⁵` | `2`-D |
| Window `Ω` | a **rhombic icosahedron** (the projection of the unit `5`-cube); fivefold-symmetric slices are the **four pentagons** of de Bruijn's picture | four pentagons in the 2-D internal space |
| Symmetry | local `D₅` (fivefold) | `D₅` |
| Prototiles | thick + thin rhombi (`2` tiles) | same |
| Inflation factor | golden ratio `τ = (1+√5)/2` (a **Pisot** number) | same |

Notes:
- de Bruijn's **pentagrid** (five families of equally spaced parallel lines at multiples of `72°`) is
  the dual of the `ℤ⁵`-projection: "the vertices of Penrose's P3 tilings can be obtained by projecting
  a window of the standard hypercubic lattice `ℤ⁵`"
  ([neverendingbooks](http://www.neverendingbooks.org/de-bruijns-pentagrids-2/)).
- The slope lives in "a four-dimensional rational subspace of `ℝ⁵` (the space **orthogonal to
  `(1,1,1,1,1)`**)" — the all-ones diagonal is the trivial direction, which is why the genuinely
  relevant data reduce from `ℝ⁵` to the `A₄`/`ℝ⁴` picture, and the de Bruijn window is drawn in
  `2`-D ([arXiv:0710.3845, *Symmetry properties of Penrose type tilings*](https://arxiv.org/pdf/0710.3845)).
- The window being a polytope (rhombic icosahedron / pentagons, measure-zero boundary) makes Penrose a
  **regular** model set ⇒ pure-point diffraction (§6).

### 5.2 Ammann–Beenker tiling (octagonal) — from `ℤ⁴`

The eightfold (octagonal) analogue of Penrose
([Wikipedia, *Ammann–Beenker tiling*](https://en.wikipedia.org/wiki/Ammann%E2%80%93Beenker_tiling);
[arXiv:1305.0879, almost-canonical model sets](https://arxiv.org/pdf/1305.0879)):

| Item | Value |
|---|---|
| Total space / lattice | `ℝ⁴`, `L = ℤ⁴` (the tesseract / `D₄`-symmetric hypercubic lattice) |
| Physical space `E∥` | `2`-D (a `D₈`-symmetric plane) |
| Internal space `H` | `2`-D (the orthogonal complement) |
| Window `Ω` | a **regular octagon** of unit edge length (the canonical projection of the unit `4`-cube), invariant under `D₈` (order 16) |
| Symmetry | `8`-fold (octagonal) |
| Prototiles | a square + a `45°` rhombus (`2` tiles) |
| Inflation factor | silver ratio `1 + √2` (a **Pisot** number) |
| Star map | Galois conjugation `√2 ↦ −√2` |

The `*`-map is defined through the images of four generating vectors `a_k ↦ a_k*`; a point is accepted
iff the integer combination of the `a_k*` lands in the octagon. Because the octagonal window is a
polytope, Ammann–Beenker is again a **regular** model set with pure-point diffraction.

### 5.3 Icosahedral (3-D) quasicrystals — from `ℤ⁶`

The physical quasicrystals (Shechtman's `Al–Mn`, etc.)
([icosahedral CPS sources, search-corroborated](https://www.sciencedirect.com/topics/chemistry/icosahedral-quasicrystal)):

| Item | Value |
|---|---|
| Total space / lattice | `ℝ⁶`; one of three hypercubic lattices — **primitive `P`**, **body-centred `I`**, **face-centred `F`** — `6` being the lowest dimension admitting a periodic lattice with icosahedral symmetry |
| Physical space `E∥` | `3`-D ("parallel" space) |
| Internal space `H` | `3`-D ("perpendicular" space) |
| Window `Ω` | a `3`-D "occupation domain" (e.g. a **triacontahedron**) in perpendicular space |
| Inflation factor | golden ratio `τ` (a **Pisot** number) |

The acceptance rule: a lattice point projects iff its `3`-D perpendicular-space image lies in the
occupation domain. "Parallel space is an **irrational cut** ⇒ the structure cannot be periodic." This
is the 3-D incarnation of the same scheme and shows the method is not tied to the plane — relevant for
the project's note that a new monotile may live "beyond the plane."

---

## 6. Pure-point diffraction and the spectrum — the window-to-Bragg dictionary

### 6.1 The theorem

**Theorem (Hof 1995; Schlottmann 2000).** *Every **regular** model set is **pure-point diffractive**:
its diffraction measure `γ̂` is a pure point (atomic) measure — a sum of Bragg peaks — with no singular
or absolutely continuous component.*

- Hof proved it for Euclidean internal spaces with polytopal windows
  ([A. Hof, *On diffraction by aperiodic structures*, Commun. Math. Phys. **169** (1995) 25–43](https://link.springer.com/article/10.1007/BF02101595)).
- Schlottmann proved it for general locally compact abelian internal spaces and general regular windows
  (M. Schlottmann, 2000), establishing **pure-point dynamical spectrum** of the hull
  ([Baake–Grimm survey, arXiv:0802.3242](https://arxiv.org/pdf/0802.3242);
  [Richard–Strungaru, *A short guide to pure point diffraction in cut-and-project sets*, arXiv:1606.08831](https://arxiv.org/pdf/1606.08831)).

This is the rigorous statement of "quasicrystal = sharp Bragg diffraction without periodicity," and it
is the mathematical content of the long-range-order certificate the project's shadow must pass.

### 6.2 Window ⇒ diffraction (explicit)

The diffraction intensities are **read directly off the window**. For a regular model set the
diffraction is supported on the dual/Fourier module, and the **Fourier–Bohr amplitude** of the Bragg
peak at a reciprocal vector `k` is given (up to density/covolume normalization) by the **Fourier
transform of the window's indicator function**, evaluated at the *star-image* `k*` of `k`
([Hof 1995; Richard–Strungaru, arXiv:1606.08831](https://arxiv.org/pdf/1606.08831);
[Baake–Grimm survey, arXiv:0802.3242](https://arxiv.org/pdf/0802.3242)):

> **`a(k)  ∝  \hat{1_W}(k*)`,  and the Bragg intensity is  `I(k) = |a(k)|² ∝ |\hat{1_W}(k*)|²`.**

So the window literally *is* the diffraction pattern, transported through the star map. The peaks live
on a **dense** module (the projection of the dual lattice `L*`) — dense Bragg spectrum is the
fingerprint of a quasicrystal, in contrast to a crystal's discrete-lattice spectrum. Modern accounts
prove the formula via the **window covariogram** (its continuity/compact support ⇒ norm-almost
periodicity of the autocorrelation ⇒ pure-point diffraction)
([Baake–Moody; arXiv:1512.00912](https://arxiv.org/pdf/1512.00912)).

### 6.3 The Pisot bridge to substitutions

Pure-point diffraction is tightly linked to the **substitution chart**: for self-similar (inflation)
tilings the inflation factor is a **Pisot** algebraic integer, and the Pisot property is the
substitution-side counterpart of pure-point diffraction (the *Pisot substitution conjecture* circle of
ideas). Penrose (`τ`), Ammann–Beenker (`1+√2`), icosahedral (`τ`) all have Pisot inflation — i.e. the
two charts (projection ↔ substitution) describe the *same* higher layer, exactly as
[`docs/APPROACH.md`](../docs/APPROACH.md) §"two charts" asserts.

---

## 7. Window geometry ↔ tiling, and how a *small* protoset (or a monotile) arises

- **The window shape controls everything downstairs.** Window symmetry becomes tiling symmetry (the
  octagonal window ⇒ `8`-fold Ammann–Beenker; the pentagonal/icosahedral window ⇒ `5`-fold Penrose).
  Window *size and offset* control density and which singular/generic tiling you get. Deforming the
  window (within measure-zero-boundary regularity) gives **deformed model sets**, still pure-point.
- **From window to a finite protoset.** With a **polytopal canonical window** the acceptance condition
  partitions internal space into finitely many cells according to *which lattice neighbours are
  simultaneously accepted*; each cell corresponds to one **local environment**, hence to one
  **prototile** (and its allowed adjacencies = **matching rules**). Finitely many cells ⇒ finitely many
  prototiles. This is why the canonical projection of `ℤⁿ` yields a small protoset (2 tiles for Penrose
  and Ammann–Beenker) rather than infinitely many shapes
  ([*Canonical projection tilings defined by patterns*, arXiv:1812.06863](https://arxiv.org/pdf/1812.06863)).
- **Toward a single prototile.** A *fractal* (non-polytopal) window can collapse the protoset to a
  **single** orbit of shapes — the route by which the hat/spectre's model-set relatives arise (§8). The
  matching rules that force aperiodicity are precisely **cocycle/window conditions** on the star map
  ([*Matching Rules as Cocycle Conditions*, arXiv:2603.13553](https://arxiv.org/pdf/2603.13553)). This
  is the lever the project pulls: *choose the higher layer (lattice + window + slope) whose shadow is a
  single prototile.*

---

## 8. Do the hat / spectre monotiles have a cut-and-project description?

**Yes — but with an important subtlety that is itself a research signal.** The 2023 aperiodic monotiles
(the **hat**, the reflection-using monotile, and the **spectre**, a strict chiral monotile needing no
reflections) are **not themselves regular model sets**, but they are **mutually locally derivable (MLD)
with / topologically conjugate to reprojections of regular model sets**:

- **Baake, Gähler, Mazáč, Mitchell — *Diffraction of the Hat and Spectre tilings and some of their
  relatives* (2025), [arXiv:2502.03268](https://arxiv.org/abs/2502.03268)** (HTML:
  [arXiv:2502.03268v1](https://arxiv.org/html/2502.03268v1)).
  - The hat and spectre tilings "are **MLD with reprojections of regular model sets**." Diffraction is
    derived for **model-set representatives** of the self-similar members of the topological conjugacy
    classes — the **CAP** (for the hat) and **CASPr** (for the spectre) tilings — which *are* regular
    model sets, then transported back to the hat/spectre by **reprojection**.
  - **Embedding:** a **Euclidean CPS of minimal dimension — physical `ℝ²` × internal `ℝ²` = `ℝ⁴`**
    (the paper notes an earlier Socolar-style projection used "two unnecessary dimensions," i.e. `6`-D).
  - **Windows are Rauzy fractals** with boundaries of **non-integer Hausdorff dimension** — *not*
    polytopes — yet still **regular** (measure-zero boundary), so the Hof–Schlottmann conclusion
    applies. The Fourier–Bohr amplitudes are therefore Fourier transforms of fractal-boundary windows
    (computed exactly via a Fourier-cocycle method).
  - **Result: the diffraction is pure point** (the hull has pure-point dynamical spectrum), explicitly
    computed. So hat/spectre are genuine quasicrystalline point sets with **no continuous spectral
    component**.

- **Baake, Gähler, Mazáč, Sadun — *On the long-range order of the Spectre tilings* (2024/2025),
  [arXiv:2411.15503](https://arxiv.org/abs/2411.15503)** (J. *Discrete Comput. Geom.*,
  [Springer](https://link.springer.com/article/10.1007/s00454-025-00756-z)): the spectre sits in a
  2-parameter family (mostly 2-tile) of topologically conjugate tilings that "have **pure point
  dynamical spectrum with continuous eigenfunctions** and may be obtained from a **`4:2`-dimensional
  cut-and-project scheme with regular windows of Rauzy-fractal type**." (Note: these Rauzy windows are
  *regular* — measure-zero, though fractal, boundary — which is why pure-point diffraction still holds.)

- **J. Smith — *Turtles, Hats and Spectres: Aperiodic structures on a Rhombic tiling* (2024),
  [arXiv:2403.01911](https://arxiv.org/abs/2403.01911)**: gives a **"cut-and-project style"**
  construction linking the **Turtle** tiling to **1-D Fibonacci words**, an alternative
  projection-based proof of non-periodicity (the hat is a deformation of the turtle, acting on the
  rhombille lattice).

**Takeaway for us.** The newest monotiles *do* fit the shadow paradigm — they are shadows of a periodic
`ℝ⁴` lattice — but their windows are **fractal**, not polytopal. That is exactly why a *single* tile
(rather than 2) suffices, and it pinpoints **the window-fractality knob** as the difference between a
classical protoset and a monotile shadow. (A genuinely *new* monotile, in the project's sense, would be
a *different* lattice/window/slope or a different Pisot factor whose fractal-windowed shadow is a single
prototile.)

---

## 9. Authoritative sources (titles + URLs)

**Foundational surveys / books**
- M. Baake, U. Grimm, C. Richard, N. Strungaru — *Aperiodic order and pure point diffraction* (survey):
  [arXiv:0802.3242](https://arxiv.org/pdf/0802.3242)
- R. V. Moody — *Model Sets: A Survey*: [arXiv:math/0002020](https://arxiv.org/pdf/math/0002020)
- M. Baake, U. Grimm — *Aperiodic Order. Vol. 1: A Mathematical Invitation* (Cambridge 2013):
  [Cambridge Core](https://www.cambridge.org/core/books/aperiodic-order/500A4C153E539E73A8146865D78737D6)
  (Vol. 2: *Crystallography and Almost Periodicity*).
- M. Baake, U. Grimm — *Mathematical diffraction of aperiodic structures*:
  [arXiv:1205.3633](https://arxiv.org/pdf/1205.3633)
- Tilings Encyclopedia (Bielefeld) — *Cut and Project* glossary:
  [tilings.math.uni-bielefeld.de/glossary/cut-and-project](https://tilings.math.uni-bielefeld.de/glossary/cut-and-project/);
  *Penrose Rhomb*:
  [tilings.math.uni-bielefeld.de/substitution/penrose-rhomb](https://tilings.math.uni-bielefeld.de/substitution/penrose-rhomb/)

**Definitions / hierarchy**
- *Meyer set* — Wikipedia: [en.wikipedia.org/wiki/Meyer_set](https://en.wikipedia.org/wiki/Meyer_set)
- *Delone set* — Wikipedia: [en.wikipedia.org/wiki/Delone_set](https://en.wikipedia.org/wiki/Delone_set)
- *Aperiodic crystal* (rational vs irrational cut) — Wikipedia:
  [en.wikipedia.org/wiki/Aperiodic_crystal](https://en.wikipedia.org/wiki/Aperiodic_crystal)
- S. Labbé — *Cut and Project Scheme* (computational, canonical window):
  [labri.fr/perso/slabbe/.../cut_and_project_scheme.html](https://www.labri.fr/perso/slabbe/docs/0.7.1/cut_and_project_scheme.html)

**Pure-point diffraction**
- A. Hof — *On diffraction by aperiodic structures*, Commun. Math. Phys. 169 (1995) 25–43:
  [Springer](https://link.springer.com/article/10.1007/BF02101595)
- C. Richard, N. Strungaru — *A short guide to pure point diffraction in cut-and-project sets*:
  [arXiv:1606.08831](https://arxiv.org/pdf/1606.08831)
- *Pure point diffraction and Poisson summation* (covariogram route):
  [arXiv:1512.00912](https://arxiv.org/pdf/1512.00912)
- Lee–Solomyak / Strungaru — *PP-diffractive substitution Delone sets have the Meyer property*:
  [arXiv:math/0510389](https://arxiv.org/pdf/math/0510389); *Why do Meyer sets diffract?*:
  [arXiv:2101.10513](https://arxiv.org/pdf/2101.10513)
- *Which Meyer sets are regular model sets?*: [arXiv:2410.22536](https://arxiv.org/pdf/2410.22536)

**Examples**
- *Ammann–Beenker tiling* — Wikipedia:
  [en.wikipedia.org/wiki/Ammann–Beenker_tiling](https://en.wikipedia.org/wiki/Ammann%E2%80%93Beenker_tiling)
- de Bruijn pentagrids:
  [neverendingbooks.org/de-bruijns-pentagrids-2](http://www.neverendingbooks.org/de-bruijns-pentagrids-2/)
- *Quasicrystals: Projections of 5-d Lattice into 2 and 3 Dimensions*:
  [arXiv:math-ph/0606028](https://arxiv.org/pdf/math-ph/0606028)
- *Symmetry properties of Penrose type tilings* (the `(1,1,1,1,1)` direction):
  [arXiv:0710.3845](https://arxiv.org/pdf/0710.3845)
- *Canonical projection tilings defined by patterns* (window cells ⇒ prototiles):
  [arXiv:1812.06863](https://arxiv.org/pdf/1812.06863)
- *Matching Rules as Cocycle Conditions*: [arXiv:2603.13553](https://arxiv.org/pdf/2603.13553)

**Hat / spectre**
- Baake, Gähler, Mazáč, Mitchell — *Diffraction of the Hat and Spectre tilings and some of their
  relatives*: [arXiv:2502.03268](https://arxiv.org/abs/2502.03268)
- *On the long-range order of the Spectre tilings*: [arXiv:2411.15503](https://arxiv.org/abs/2411.15503)
  / [Springer DCG](https://link.springer.com/article/10.1007/s00454-025-00756-z)
- J. Smith — *Turtles, Hats and Spectres: Aperiodic structures on a Rhombic tiling*:
  [arXiv:2403.01911](https://arxiv.org/abs/2403.01911)

---

## 10. Relevance to our shadow / strict-extension approach

This section maps the standard cut-and-project theory above **directly** onto the project's vocabulary
in [`docs/APPROACH.md`](../docs/APPROACH.md) and [`docs/CERTIFICATE.md`](../docs/CERTIFICATE.md). The
correspondence is exact, not analogical — the project's "projection chart" **is** a CPS.

### 10.1 The dictionary

| Project term (SBT) | Cut-and-project object | Where |
|---|---|---|
| **Higher layer** (lawful, periodic, simple "upstairs") | the **lattice `L ⊂ ℝⁿ`** in the total space `ℝ^d ⊕ H` | §2.1 |
| **Shadow / down-projection** (`projection = shadow`) | the **physical projection `π`** restricted to accepted points; `⋏(W) = {π(x) : x ∈ L, x* ∈ W}` | §2.3 |
| **Acceptance window `Ω`** | the **window `W ⊂ H`** (atomic surface / occupation domain) | §2.3 |
| **The internal complement** | the **internal/perpendicular space `H = E⊥`** | §2.1 |
| **Non-descending object `U`** = the **irrational projection direction** (= `√2 ∉ ℚ` "wearing a geometric hat") | the **irrational slope of `E∥`**, equivalently the dense star-image `𝓛* = π_int(L)`; on the substitution side, the **Pisot inflation factor** (`τ`, `1+√2`, …) acting via Galois conjugation `√d ↦ −√d` | §2.2, §3, §6.3 |
| **Audited descent `C(U) ↓ a♯`** | the **cut-and-project map run forwards** — a *derivation*, not an inverse search (you compute the shadow; you don't hunt the plane) | §2.3 |
| **Factor through the torus `ℝⁿ/L`** (shadow law F33/F34) | the model set **factors through the lattice torus**; its dynamical hull is a **factor of the torus `(ℝ^d×H)/L`** — the maximal equicontinuous factor — which is *exactly* the pure-point (Bragg) structure | §6 |
| **Long-range-order certificate** | **pure-point diffraction** of a **regular** model set (Hof–Schlottmann) | §6.1 |
| **Two dual charts (F41)** | **projection chart** (lattice + window + slope) ↔ **substitution chart** (Pisot inflation); linked by pure-point diffraction ↔ Pisot | §6.3 |
| **A "new monotile" upstairs** | a **new `(L, W, E∥)` triple** (or new Pisot factor) whose shadow `⋏(W)` is a **single prototile** | §7 |

### 10.2 The irrational direction is *literally* the non-descending object

§3 is the rigorous content of [`APPROACH.md`](../docs/APPROACH.md) §"The non-descending object." A
**rational** slope **descends** to a periodic shadow (a lattice plane); an **irrational** slope **does
not descend** to any periodic direction — it forces `π_int(L)` dense and kills every translation period
while preserving repetitivity. The "non-descending object `U`" of the framework is precisely this
irrational slope (equivalently the Pisot inflation factor reached through Galois conjugation). The
slope cannot be reduced to a rational one *by definition of irrationality* — that is the mathematical
meaning of "non-descending."

### 10.3 The strict-extension / non-factorization certificate, in CPS terms

The project's certificate (F8; *"the higher-layer map `π₁` does not factor through the local-plane map
`π₀`"* ⟺ *"two patches with `π₀` equal but `π₁` different"* — a **fiber-collision-with-split**) is the
finite, computable signature that the shadow genuinely came from a higher layer. In CPS language:

- `π₀` = the **local-plane (finite-patch) view** of the tiling;
- `π₁` = the **hierarchical/star-coordinate view** — the global position via `x* ∈ H` and the
  inflation structure.

**Local indistinguishability** (two patches identical under `π₀`) **with globally forced hierarchy**
(distinct `x*` / distinct inflation lineage, so distinct under `π₁`) is exactly the hallmark of
aperiodic order — and it is **non-trivial only when the window cut is irrational**. For a rational
slope the shadow is periodic, `π₁` *does* factor through `π₀` (everything is determined locally up to
translation), and the certificate **fails** — correctly flagging "this is a within-plane artifact, not
a higher-layer shadow." So the certificate is precisely a test that the CPS is non-degenerate
(irrational slope, dense `𝓛*`), i.e. that the object is a true model set and not a crystal. This is the
"strict extension / non-factorization" criterion the walk must land.

### 10.4 Where the hat/spectre evidence points the walk

§8 is directly load-bearing: the hat and spectre **are** shadows of a periodic `ℝ⁴` lattice (minimal
CPS), pure-point diffractive, but with **fractal (Rauzy) windows** — and that fractality is exactly
what reduces the protoset to a **single** tile. So the project's target — *a higher layer whose audited
shadow is a new monotile* — is, in this chart, the search for a **new lattice/window/slope (or new
Pisot factor) with a window whose acceptance cells collapse to one prototile**. The hat/spectre show
the regime exists (fractal-windowed monotile shadows in `ℝ⁴`); a genuinely new monotile means a new
point in that `(L, W, E∥)` / Pisot space — possibly at a different symmetry order or beyond the plane
(the `ℤ⁶` icosahedral case in §5.3 shows the method is dimension-agnostic). The walk's job, per
[`METHODOLOGY.md`](../docs/METHODOLOGY.md), is to reach that layer and **project down as an audited
shadow**, with §6.1 pure-point diffraction (long-range order) and §10.3 non-factorization (genuine
higher-layer origin) as the two acceptance gates.
