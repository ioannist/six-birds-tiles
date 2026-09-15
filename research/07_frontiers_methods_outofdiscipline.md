# 07 — Frontiers, Computational Search Methods, and Cross-Disciplinary Lenses

*Breadth pillar for the six-birds-tiles program. Compiled June 2026 from live web research; every load-bearing claim carries an inline source URL. The closing section maps each finding onto our "tile = audited shadow of a higher layer / strict-extension certificate" attack.*

---

## Overview

Three things are true at once, and the tension between them is exactly where our project lives:

1. **The headline planar Euclidean question is closed.** A single, undecorated, simply-connected tile that forces aperiodicity exists: the **hat** (March 2023) and, removing the reflection loophole, the **spectre** / **Tile(1,1)** (May 2023), by Smith, Myers, Kaplan & Goodman-Strauss. ([arXiv:2303.10798](https://arxiv.org/abs/2303.10798), [arXiv:2305.17743](https://arxiv.org/abs/2305.17743), both published in *Combinatorial Theory* in 2024.)
2. **The discovery was a human–computer hybrid, and the toolchain is small, open, and reusable.** A hobbyist's hand-tinkering on a kite grid + Kaplan's tiling code (with `SAT`-solver and substitution-verification machinery) + a hand proof. The software is mostly browser-based JavaScript and a short Python verifier — not an industrial search engine.
3. **The frontier is wide open the moment you leave the flat plane with reflections allowed.** Strongly aperiodic **convex** monotiles in the **hyperbolic plane**, **strongly** aperiodic **3D** monotiles (Schmitt–Conway–Danzer is only *weakly* aperiodic), and various decorated/colored/group-theoretic settings are unresolved as of 2026.

The deep structural fact that makes our specific strategy more than a metaphor: **aperiodic order is *natively* a projection-from-higher-dimension discipline.** The two dominant model classes — **cut-and-project / model sets** (slice a lattice in ℝⁿ, project at an irrational slope) and **primitive substitution / inflation** systems — are *dual descriptions of the same objects*, glued together by **Pisot algebraic integers**, and inflation is literally a **renormalization-group fixed point**. That is the project's APPROACH.md "two charts" picture, and it is mainstream mathematics (Baake–Grimm school), not a private formalism.

---

## 1. The discovery / search methods & software

### 1.1 How the hat and spectre were actually found

- **The human step.** David Smith, a retired print technician, explored polyforms by hand on a **kite grid** (each hexagon cut into 6 kites; shapes made of glued kites are *polykites*). The hat is the **"T(8)" 8-kite polykite** — a 13-sided polygon. Smith physically cut and arranged paper tiles, noticed "The Anomaly" (patches that kept growing without forcing periodicity), and got stuck building large patches. Kaplan's own retrospective stresses this was *empirical exploration, not theoretical prediction*. ([Kaplan, "The Path to Aperiodic Monotiles," arXiv:2509.12216, Sept 2025](https://arxiv.org/abs/2509.12216); [isohedral.ca/aperiodic-monotiles](https://isohedral.ca/aperiodic-monotiles/))
- **The computer step.** Smith turned to **Kaplan's tiling software** (Heesch-number / patch-growth tooling) to grow and check large patches. Kaplan's quote: *"Through a combination of hand tinkering and computer analysis (made possible because of additions to my tiling code by undergraduate researcher **Ava Pun**), Dave and I quickly determined that The Anomaly was real."* ([isohedral.ca/aperiodic-monotiles](https://isohedral.ca/aperiodic-monotiles/))
- **The proof step (two independent routes):**
  1. **Substitution / metatile hierarchy** (Kaplan). The hat clusters into four **metatiles** labelled **H, T, P, F**; these obey a substitution (inflation) rule, and the forced hierarchy of supertiles proves non-periodicity. The shape sits in a **one-parameter continuum** `Tile(a,b)` of combinatorially equivalent polygons (the hat is `Tile(1,√3)`, the "turtle" `Tile(√3,1)`, the spectre's base is `Tile(1,1)`). ([arXiv:2303.10798](https://arxiv.org/abs/2303.10798))
  2. **Computer-assisted "not-a-weak-isohedral-number / combinatorial" argument** (Myers). A finite, exhaustive **case analysis** verified by a short program, giving a second, independent aperiodicity proof. Downloadable **Python verification code** accompanies the paper. ([cs.uwaterloo.ca/~csk/hat](https://cs.uwaterloo.ca/~csk/hat/))
- **The spectre upgrade.** The hat needs *reflected* copies. Tile(1,1) lies at the symmetric midpoint of the continuum and is *weakly chiral* (tiles non-periodically **if** reflections are forbidden). Curving its edges yields the **Spectre**, a **strictly chiral** monotile: it admits *only* chiral non-periodic tilings *even when reflections are allowed*. The proof goes through a bijection (Thm 3.1) between hat–turtle tilings and spectre tilings. ([arXiv:2305.17743](https://arxiv.org/abs/2305.17743); [cs.uwaterloo.ca/~csk/spectre](https://cs.uwaterloo.ca/~csk/spectre/))

### 1.2 The actual software stack (all open, all small)

| Tool | What it is | Link |
|---|---|---|
| **HatViz** | P5.js browser app: build hat patches, show metatile/supertile outlines, slide the shape continuum. BSD-3. | [github.com/isohedral/hatviz](https://github.com/isohedral/hatviz) |
| **Hat homepage** | Interactive patch builder, H7/H8 substitution constructor, **downloadable Python verifier** for the case analysis. | [cs.uwaterloo.ca/~csk/hat](https://cs.uwaterloo.ca/~csk/hat/) |
| **Spectre homepage** | Tile(1,1) patch builder, SVG outlines, hat↔spectre equivalence animation. | [cs.uwaterloo.ca/~csk/spectre](https://cs.uwaterloo.ca/~csk/spectre/) |
| **christianp/aperiodic-monotile** | Hat & spectre outlines in many formats (SVG/etc.) — the de-facto "asset" repo. | [github.com/christianp/aperiodic-monotile](https://github.com/christianp/aperiodic-monotile) |
| **nhatcher/hats + splr-wasm** | Encodes hat/turtle/spectre tiling as **SAT (CNF)** and solves it in-browser with the Rust solver **`splr`** compiled to WebAssembly. Excellent worked example of the SAT encoding. | [github.com/nhatcher/hats](https://github.com/nhatcher/hats), [splr-wasm](https://github.com/nhatcher/splr-wasm), writeup: [nhatcher.com/post/on-hats-and-sats](https://www.nhatcher.com/post/on-hats-and-sats/) |
| **vmagnin/hat_polykite** | Fortran/Cairo batch SVG generator (laser-cutting puzzles). | [github.com/vmagnin/hat_polykite](https://github.com/vmagnin/hat_polykite) |

### 1.3 Kaplan's SAT-solver line: deciding tileability by reduction to Boolean satisfiability

This is the most directly relevant *general* method, and it predates the hat:

- **Heesch numbers of unmarked polyforms** (Kaplan, *Contributions to Discrete Math.*, 2022; [arXiv:2105.09438](https://arxiv.org/abs/2105.09438); [project page](https://isohedral.ca/heesch-numbers-of-unmarked-polyforms/)). The **Heesch number** = how many concentric coronas of copies you can place around a tile before being forced to leave a gap (a finite, *local* obstruction to tiling). On a suggestion from **Bram Cohen**, Kaplan encodes *"does this shape admit ≥ n coronas?"* as a Boolean formula — variables = candidate placements of copies, clauses = no-overlap + no-gap — and hands it to **CryptoMiniSat** (~0.15 s/shape). Data: polyominoes ≤ 19, polyhexes ≤ 17, polyiamonds ≤ 24; Heesch numbers up to 4. Dataset at [cs.uwaterloo.ca/~csk/heesch](https://cs.uwaterloo.ca/~csk/heesch/).
- **Detecting Isohedral Polyforms with a SAT Solver** (Kaplan, 2024; [arXiv:2406.16407](https://arxiv.org/abs/2406.16407)). Expresses *"does this polyform tile the plane isohedrally?"* as a single SAT instance. This is the closest off-the-shelf decision procedure for the **periodic-candidate-elimination** step.
- The SAT encoding generalizes (Hatcher): on an M×N hex grid, `12·M·N` Booleans (hat / anti-hat × 6 rotations per hex), clauses for no-collision + full-coverage; ~75 columns / 4 tiles ≈ 5.5M clauses, solvable in ~an hour. ([nhatcher.com](https://www.nhatcher.com/post/on-hats-and-sats/))

### 1.4 Substitution-tiling software (for the inflation chart)

- **Sage** ships a `TilingSolver` / `Polyomino` combinatorics module (exact-cover / dancing-links style). ([doc.sagemath.org/.../tiling](https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/tiling.html))
- **Wolfram Function Repository — `AlgebraicSubstitutionTiling`** generates multi-level substitution tilings (incl. Penrose). ([resource](https://resources.wolframcloud.com/FunctionRepository/resources/AlgebraicSubstitutionTiling/))
- **GROUT** — C++ GUI for combinatorial/topological invariants of 1D primitive symbolic substitutions. ([arXiv:1512.00398](https://arxiv.org/pdf/1512.00398))
- **Tilings Gap-Distribution / Pair-Correlation project** — Sage/Python API over 40+ named tilings. ([UW WXML](https://sites.math.washington.edu//wxml/tilings/index.php))

---

## 2. Computational, SAT/SMT & decidability approaches; computer-assisted proofs

### 2.1 The decidability backbone (the domino problem)

Aperiodic tile *sets* and *undecidability* are two faces of one coin (the survey [Bruneau & Whittaker, "Planar aperiodic tile sets: from Wang tiles to the Hat and Spectre," arXiv:2310.06759](https://arxiv.org/abs/2310.06759) is the clean modern overview):

| Year | Result | Tiles |
|---|---|---|
| 1961 | **Wang** poses the Domino Problem; conjectures "tiles ⇒ tiles periodically." | — |
| 1966 | **Berger**: Domino Problem **undecidable**; first aperiodic Wang set. | 20,426 (later 104) |
| 1971 | **Robinson**: simpler undecidability proof + aperiodic set. | 6 |
| 1974 | **Penrose** (kite/dart, rhombs). | 2 |
| 1996 | **Kari–Culik**: number-theoretic (Beatty/multiplicative) construction. | 13 |
| 2015 | **Jeandel–Rao**: minimal aperiodic Wang set, by **exhaustive computer search**. | **11 tiles / 4 colors (proved minimal)** |
| 2023 | **Hat / Spectre**: aperiodic *monotile*. | 1 |

- **Jeandel–Rao** is the canonical *computer-assisted minimality* result: an exhaustive enumeration of all Wang sets up to 11 tiles, ~**1 CPU-year on several hundred cores**, cross-checked with multiple independently-written programs to guard against bugs. ([arXiv:1506.06492](https://arxiv.org/abs/1506.06492); substitutive structure later given in [arXiv:1808.07768](https://arxiv.org/abs/1808.07768))
- Berger's reduction (Turing machine → tile set that tiles iff TM doesn't halt) is *why* aperiodic sets must exist and *why* tileability is undecidable in general — the foundational link between **computation** and **tiling**.

### 2.2 The 2022–2025 decidability frontier (Greenfeld–Tao and successors)

This is the live research front on *which* tiling questions are even algorithmically answerable:

- **Greenfeld–Tao, "A counterexample to the periodic tiling conjecture"** ([arXiv:2211.15847](https://arxiv.org/abs/2211.15847), *Annals of Math.* 2024; [announcement arXiv:2209.08451](https://arxiv.org/abs/2209.08451); [Tao's blog](https://terrytao.wordpress.com/2022/11/29/a-counterexample-to-the-periodic-tiling-conjecture-2/)). A **single** tile (a finite subset of ℤ² × G₀, G₀ a finite abelian 2-group) that tiles **only aperiodically** — disproving the Grünbaum–Shephard / Lagarias–Wang **periodic tiling conjecture** in high enough dimension. Method: encode a "**Sudoku**" of 2-adically-structured functional equations as one tiling equation. *This is itself a higher-structure → tiling projection.*
- **Greenfeld–Tao, "Undecidability of translational monotilings"** (*J. Eur. Math. Soc.*, 2025; [Tao's blog](https://terrytao.wordpress.com/2023/09/18/undecidability-of-translational-monotilings/)): for a *single* tile in high dimension, even tileability is **undecidable**.
- **Decidable side**: the periodic tiling conjecture *holds* in 2D (**Bhattacharya**), so 2D translational tileability of a single set is **decidable**; and Greenfeld et al. prove it for **rational polygons**, giving decidability there ([arXiv:2408.02151](https://arxiv.org/abs/2408.02151), *Expo. Math.* 2024).
- **Undecidability with very few/simple tiles** keeps tightening: **Demaine–Langerman, "Tiling with three polygons is undecidable"** ([arXiv:2409.11582](https://arxiv.org/abs/2409.11582)); undecidability with orthogonally-convex polyominoes ([arXiv:2506.12726](https://arxiv.org/abs/2506.12726)); 5-polyomino sets ([Y. Kim, 2025]).

**Take-away for us:** the *general* inverse problem ("find a tile that tiles only aperiodically") is undecidable, so a brute-force planar search has no completeness guarantee — which is precisely APPROACH.md's argument for working *upstairs* (in a setting where the object is forced/lawful) and projecting down, rather than searching shapes. SAT/SMT is excellent for the **finite audit** (eliminate periodic candidates up to size N, verify a corona/patch), not for the unbounded existence question.

### 2.3 SMT / constraint generalizations

Beyond pure SAT, tileability questions map naturally to **SMT** (e.g. linear-arithmetic theories for geometric placement) and to **exact-cover / ILP**. The Heesch and isohedral encodings above are the proven instances; metallic-mean Wang-tile work frames aperiodic tilesets as **aperiodic "computer chips"** / self-similar substitutions ([arXiv:2312.03652](https://arxiv.org/pdf/2312.03652), [arXiv:2403.03197](https://arxiv.org/pdf/2403.03197)), tying the SAT/automata view back to inflation.

---

## 3. The frontier of "new monotiles" — where genuine novelty is still open

A precise map of solved vs. open. **The planar-Euclidean headline is closed; almost everything else is open.**

### 3.1 Planar Euclidean — essentially closed, but with residual open variants
Solved: simply-connected undecorated monotile, reflections allowed (**hat**) and reflections-forbidden / strictly-chiral (**spectre**). Residual open questions explicitly listed in the literature ([emergentmind topic](https://www.emergentmind.com/topics/aperiodic-monotile), [Kaplan arXiv:2509.12216](https://arxiv.org/abs/2509.12216)):
- Does a **disk-like monotile with a *unique* aperiodic tiling class** exist (vs. the hat's continuum)?
- Does a **chiral disk-like monotile using only rotations+translations** that defines a *unique* aperiodic class exist?
- Classification: how many "essentially different" aperiodic monotiles are there; is there an infinite family?
- Long-range order / spectral nature of spectre tilings is still being pinned down ([On the Long-Range Order of the Spectre Tilings, *Discrete & Comput. Geom.* 2025](https://link.springer.com/article/10.1007/s00454-025-00756-z); homochiral inflation [arXiv:2502.15608](https://arxiv.org/abs/2502.15608); dynamics/topology [arXiv:2305.05639](https://arxiv.org/abs/2305.05639)).

### 3.2 Hyperbolic plane — **the most reachable open frontier for "a strongly aperiodic *convex monotile*"**
- **Böröczky (1974)**: a **weakly** aperiodic monotile in ℍ² (the "binary tiling" — tiles, but only with non-compact-quotient symmetry).
- **Margulis–Mozes**: aperiodic tilings of ℍ² by **convex** polygons (single convex tile, *weak* sense). ([Inventiones-adjacent / Semantic Scholar](https://www.semanticscholar.org/paper/593a4c2c1fa9ac479b0e99dcced606842db34ee8))
- **Goodman-Strauss (2005, *Inventiones*)**: first **strongly** aperiodic *set* of tiles in ℍ² (no infinite cyclic symmetry); later a **hierarchical** strongly-aperiodic set ([Inventiones 2005](https://link.springer.com/article/10.1007/s00222-004-0384-1); [Theoret. Comput. Sci. 2010](https://www.sciencedirect.com/science/article/pii/S0304397509008123)). Also proved the ℍ² Domino Problem undecidable using **regular polygons**.
- **Maiti, "Unboundedness of the Heesch Number for Hyperbolic Convex Monotiles"** ([arXiv:2603.27827](https://arxiv.org/abs/2603.27827), v2 **19 May 2026**): constructs an **infinite family of aperiodic convex monotiles in ℍ² with inner angles that are rational multiples of π**, and shows hyperbolic Heesch numbers are unbounded — a fundamental Euclidean/hyperbolic difference. **Crucially, its "Discussion and Open Problems" leaves open whether a *strongly aperiodic convex monotile* exists in ℍ².**

> **This is the single best-defined, currently-open, monotile-existence target.** Confirmed open as of mid-2026: *"It is challenging to prove or disprove the existence of a strongly aperiodic … convex polygon in the hyperbolic plane."* Aperiodic *convex* monotiles exist (weak); a *strongly* aperiodic convex monotile is unresolved. Related: [Mann, "Hyperbolic regular polygons with notched edges"](https://faculty.washington.edu/cemann/hyperbolic_reg_polygons.pdf).

### 3.3 Three dimensions and higher — **strongly aperiodic 3D monotile is open**
- **Schmitt–Conway–Danzer (SCD) biprism** (Schmitt 1988; Conway & Danzer convexified it): a single convex prototile that tiles ℝ³ with **no translational symmetry** — but only **weakly** aperiodic, because its tilings admit a **screw symmetry** (rotation∘translation along an axis), which many consider "too close to periodic." ([Einstein problem — Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem))
- **Open:** a **strongly** aperiodic 3D monotile (no infinite cyclic symmetry of any kind). Whether the hat/spectre method lifts to a 3D solid is explicitly flagged by Kaplan as a future direction. In *higher* dimensions aperiodicity becomes *more* common (Greenfeld–Tao's counterexample lives there), so the difficulty is the *single convex solid in ℝ³* sweet spot.

### 3.4 Other open settings (rotations-only, decorated, group-theoretic, other manifolds)
- **Group-theoretic monotiles** — a genuinely new lens. **Coulbois, Gajardo, Guillon, Lutfalla, "Aperiodic monotiles: from geometry to groups"** ([arXiv:2409.15880](https://arxiv.org/abs/2409.15880), rev. Nov 2025) unifies the **hat** and the **Greenfeld–Tao** counterexample under one framework and turns the hat into a **new aperiodic *group* monotile**. Aperiodic subshifts/SFTs on **hyperbolic groups**, **surface groups**, and the **discrete Heisenberg group** are an active front ([Cambridge Core](https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/strongly-aperiodic-subshifts-of-finite-type-on-hyperbolic-groups/28C2F3E72DD95F8A4678367BCB35685E); [arXiv:1510.06439](https://arxiv.org/pdf/1510.06439); [arXiv:2009.07751](https://arxiv.org/pdf/2009.07751)).
- **Colored / decorated / matching-rule monotiles** (Taylor–Socolar 2010, [arXiv:1009.1419](https://arxiv.org/pdf/1009.1419)) remain a fertile class once you relax "undecorated."
- **Other manifolds / non-Euclidean ambient spaces** — largely untouched as monotile questions.

---

## 4. Renormalization-group & cross-disciplinary "projection-from-higher-dimension" lenses

This is the part most directly aligned with the project's `F35` (scale descent / renormalization) and `F41` (projection↔substitution duality).

### 4.1 Inflation as a renormalization-group fixed point
- An **inflation rule** = rescale prototiles by factor λ, then dissect each rescaled tile back into original prototiles. The **substitution matrix** M counts how many of each prototile appears; its **Perron–Frobenius eigenvalue equals λ** (or λ², for areas) and the **left/right eigenvectors give the asymptotic tile/patch frequencies**. ([Baake–Grimm school](https://oro.open.ac.uk/71195/8/ae5086.pdf))
- **Inflation = RG fixed point.** Applying the renormalization (de-inflation) operation returns the tiling to itself up to scale — this self-similarity *is* a fixed point of an RG-style map, which is *why* inflation produces deterministic, statistically self-similar, hyperuniform structures. ([Mazáč, "Exact renormalisation for patch frequencies in inflation systems," arXiv:2507.07753, 2025](https://arxiv.org/abs/2507.07753); [Baake–Gähler–Mañibo, "Pair correlations of aperiodic inflation rules via renormalisation," arXiv:1511.00885](https://arxiv.org/pdf/1511.00885); [hyperuniformity & number rigidity, arXiv:2310.20517](https://arxiv.org/pdf/2310.20517))
- The **renormalization cocycle** transports patch frequencies / diffraction data between scales **exactly** (a closed algebraic system, not an approximation) — the rigorous RG content. ([arXiv:2507.07753](https://arxiv.org/abs/2507.07753); diffraction scaling near origin [arXiv:1905.04177](https://arxiv.org/pdf/1905.04177))
- This is the literal mathematical home of our **T1 (Perron-eigenvalue *drive* certificate)** and **T2 (stacking-composition across inflation levels)**: a drive certificate is a statement about the spectral radius / contraction of the renormalization map, and "strict at every level" is RG-tower stability.

### 4.2 Cut-and-project as a dynamical system; the projection ↔ substitution duality
- **Model sets / cut-and-project**: physical space E∥ ⊂ ℝⁿ, internal/perp space E⊥, lattice L, window Ω; select lattice points whose E⊥-image lands in Ω, project to E∥. **Rational slope → periodic; irrational slope → aperiodic.** ([Baake et al., "Aperiodic order and pure point diffraction," arXiv:0802.3242](https://arxiv.org/pdf/0802.3242))
- The **tiling/hull dynamical system** (translation action on the orbit closure) is the dynamical-systems object; **pure-point dynamical spectrum ⇔ pure-point diffraction** is the central equivalence, and model sets sit inside the **pure-point-diffractive** class. ([arXiv:0712.1323](https://arxiv.org/pdf/0712.1323))
- **Substitution ⇔ projection are not really different classes** for pure-point-diffractive models — they describe the same objects. ([arXiv:0802.3242](https://arxiv.org/pdf/0802.3242)) This is APPROACH.md's **F41 duality** as established theorem, and "inflation vs projection sets" is studied head-on ([Baake–Grimm–Mañibo, oro.open.ac.uk/71195](https://oro.open.ac.uk/71195/8/ae5086.pdf)).

### 4.3 Number theory: Pisot / Salem numbers, β-expansions, Rauzy fractals
- **Pisot numbers are the bridge.** A real algebraic integer >1 whose other Galois conjugates lie strictly inside the unit disk. The **Pisot Substitution Conjecture**: a primitive Pisot-inflation substitution has **pure discrete (pure-point) spectrum**. Any Pisot/Salem number is the dilation of some **Meyer set**. ([Akiyama et al., "Meyer sets, Pisot numbers, and self-similarity in symbolic dynamical systems," arXiv:2404.04116](https://arxiv.org/html/2404.04116v1))
- **β-expansions / β-substitutions**: for β a **Pisot simple Parry number**, the β-substitution's tiling dynamical system has **pure discrete spectrum**; the **Rauzy fractal** is the internal-space window — i.e. the cut-and-project window *is* a number-theoretic object. ([arXiv:1907.11012, "Fourier transform of Rauzy fractals and point spectrum of 1D Pisot inflation tilings"](https://arxiv.org/pdf/1907.11012); [Cut-and-Project Schemes for Pisot Family Substitution Tilings, *Symmetry* 2018](https://www.mdpi.com/2073-8994/10/10/511))
- **Directly relevant to CERTIFICATE.md field 4**: the inflation factor's *trace, norm, and characteristic polynomial are rational Galois invariants* while the leading eigenvalue is an irrational Pisot number — exactly the `√2`-wearing-a-hat `InvDesc/AggInv` profile. This is standard algebraic-number-theory of substitution matrices.

### 4.4 ML / heuristic search for combinatorial geometry
- **TilinGNN** ([arXiv:2007.02278](https://arxiv.org/pdf/2007.02278)): a **self-supervised graph neural network** that learns to tile a region given a tile set — direct evidence that learned heuristics can drive combinatorial tiling search (placement as a graph node-selection problem).
- **AlphaTensor** ([Nature 2022, arXiv-linked](https://www.nature.com/articles/s41586-022-05172-4)): the archetype for **RL discovering provably-correct mathematical objects** in an astronomically large discrete action space (>10¹² actions) by AlphaZero-style search + neural guidance — the template for "agent searches a structured space, certificate verifies the find." Conceptually the closest existing analogue to *our* "agent walks theory space, finite audit certifies."
- General pattern: **neural-guided search + an exact verifier (SAT/finite check)** is the modern recipe — guidance is heuristic, correctness is delegated to a decidable audit. Mirrors our "walk (heuristic) + SAU six-field certificate (decidable)."

---

## 5. Knowledge-base catalogues (the substitution-tiling "reference DB")

- **Tilings Encyclopedia** — [tilings.math.uni-bielefeld.de](https://tilings.math.uni-bielefeld.de/). Maintained by **Dirk Frettlöh, Franz Gähler, Edmund Harriss**. The standard online catalogue of **nonperiodic substitution tilings**. Each entry: image, the substitution/inflation rule, **inflation factor**, symmetry (e.g. dihedral, finite rotations), properties tags (*self-similar substitution, finite local complexity, finite rotations*), tile type (rhombs, polytopal, fractal), and literature references. Searchable by name ("Penrose", "fractal") and by person. CC BY-NC-SA; web interface only (no API/bulk export advertised). **This is the obvious enumeration target for "which higher-layer/inflation-factor combinations are already realized as a monotile shadow."**
- **Baake & Grimm, *Aperiodic Order*** (Cambridge, *Encyclopedia of Mathematics and its Applications*): **Vol. 1 — A Mathematical Invitation** (No. 149, 2013) and **Vol. 2 — Crystallography and Almost Periodicity** (No. 166, 2017). The authoritative monograph for cut-and-project, substitution/inflation, diffraction, renormalization — i.e. the textbook backbone of §4.
- **A Computer Search for Planar Substitution Tilings with n-Fold Rotational Symmetry** (Gähler, Kwan, Maloney, *Discrete & Comput. Geom.* 2014; [arXiv:1404.5193](https://arxiv.org/abs/1404.5193)): an *algorithmic generator* of substitution rules on triangles with angles ∈ (π/n)·ℤ — finds new 7-fold rules at many inflation factors. Builds on **Harriss**'s rhomb-substitution work. A concrete "search the substitution chart by computer" precedent.
- **Software hubs** already listed in §1.2/§1.4 (HatViz, Sage `TilingSolver`, Wolfram `AlgebraicSubstitutionTiling`, GROUT, UW pair-correlation API) double as small structured datasets.
- **Kaplan's `isohedral.ca`** and the **hat/spectre project pages** function as a curated, code-backed mini-catalogue for the monotile case specifically.

---

## 6. Authoritative sources (titles + URLs)

**Discovery & software**
- Smith, Myers, Kaplan, Goodman-Strauss, *An aperiodic monotile* — [arXiv:2303.10798](https://arxiv.org/abs/2303.10798) · [hat homepage](https://cs.uwaterloo.ca/~csk/hat/)
- Smith, Myers, Kaplan, Goodman-Strauss, *A chiral aperiodic monotile* — [arXiv:2305.17743](https://arxiv.org/abs/2305.17743) · [spectre homepage](https://cs.uwaterloo.ca/~csk/spectre/)
- Kaplan, *The Path to Aperiodic Monotiles* — [arXiv:2509.12216](https://arxiv.org/abs/2509.12216)
- Kaplan, *Aperiodic Monotiles* (overview) — [isohedral.ca/aperiodic-monotiles](https://isohedral.ca/aperiodic-monotiles/)
- HatViz — [github.com/isohedral/hatviz](https://github.com/isohedral/hatviz) · outlines [github.com/christianp/aperiodic-monotile](https://github.com/christianp/aperiodic-monotile)
- Hatcher, *The Hat, the Spectre and SAT solvers* — [nhatcher.com/post/on-hats-and-sats](https://www.nhatcher.com/post/on-hats-and-sats/) · [github.com/nhatcher/hats](https://github.com/nhatcher/hats)

**SAT/SMT & decidability / computer-assisted proofs**
- Kaplan, *Heesch numbers of unmarked polyforms* — [arXiv:2105.09438](https://arxiv.org/abs/2105.09438) · [project](https://isohedral.ca/heesch-numbers-of-unmarked-polyforms/)
- Kaplan, *Detecting Isohedral Polyforms with a SAT Solver* — [arXiv:2406.16407](https://arxiv.org/abs/2406.16407)
- Jeandel & Rao, *An aperiodic set of 11 Wang tiles* — [arXiv:1506.06492](https://arxiv.org/abs/1506.06492)
- Bruneau & Whittaker, *Planar aperiodic tile sets: from Wang tiles to the Hat and Spectre* — [arXiv:2310.06759](https://arxiv.org/abs/2310.06759)
- Greenfeld & Tao, *A counterexample to the periodic tiling conjecture* — [arXiv:2211.15847](https://arxiv.org/abs/2211.15847) (*Annals* 2024)
- Greenfeld & Tao, *Undecidability of translational monotilings* — [Tao blog](https://terrytao.wordpress.com/2023/09/18/undecidability-of-translational-monotilings/) (*JEMS* 2025)
- Greenfeld et al., *Periodicity and decidability of translational tilings by rational polygonal sets* — [arXiv:2408.02151](https://arxiv.org/abs/2408.02151)
- Demaine & Langerman, *Tiling with three polygons is undecidable* — [arXiv:2409.11582](https://arxiv.org/abs/2409.11582)

**Frontier settings**
- Maiti, *Unboundedness of the Heesch Number for Hyperbolic Convex Monotiles* — [arXiv:2603.27827](https://arxiv.org/abs/2603.27827) (May 2026)
- Goodman-Strauss, *A strongly aperiodic set of tiles in the hyperbolic plane* — [Inventiones 2005](https://link.springer.com/article/10.1007/s00222-004-0384-1)
- Goodman-Strauss, *A hierarchical strongly aperiodic set of tiles in the hyperbolic plane* — [TCS 2010](https://www.sciencedirect.com/science/article/pii/S0304397509008123)
- Coulbois, Gajardo, Guillon, Lutfalla, *Aperiodic monotiles: from geometry to groups* — [arXiv:2409.15880](https://arxiv.org/abs/2409.15880)
- Imperor-Clerc & Sadoc, *Homochiral inflation for the aperiodic monotile Tile(1,1)* — [arXiv:2502.15608](https://arxiv.org/abs/2502.15608)
- *On the Long-Range Order of the Spectre Tilings* — [*DCG* 2025](https://link.springer.com/article/10.1007/s00454-025-00756-z)
- *Einstein problem* (history hub) — [Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem)

**RG / cross-disciplinary**
- Mazáč, *Exact renormalisation for patch frequencies in inflation systems* — [arXiv:2507.07753](https://arxiv.org/abs/2507.07753) (2025)
- Baake, Gähler, Mañibo, *Pair correlations of aperiodic inflation rules via renormalisation* — [arXiv:1511.00885](https://arxiv.org/pdf/1511.00885)
- Baake et al., *Aperiodic order and pure point diffraction* — [arXiv:0802.3242](https://arxiv.org/pdf/0802.3242)
- Akiyama et al., *Meyer sets, Pisot numbers, and self-similarity in symbolic dynamical systems* — [arXiv:2404.04116](https://arxiv.org/html/2404.04116v1)
- *Cut-and-Project Schemes for Pisot Family Substitution Tilings* — [*Symmetry* 2018](https://www.mdpi.com/2073-8994/10/10/511)
- Baake & Grimm, *Aperiodic Order*, Vols. 1–2 (Cambridge EMA 149 & 166)
- Lin et al., *TilinGNN: Learning to Tile with a Self-Supervised GNN* — [arXiv:2007.02278](https://arxiv.org/pdf/2007.02278)
- Fawzi et al., *Discovering faster matrix multiplication algorithms with RL (AlphaTensor)* — [Nature 2022](https://www.nature.com/articles/s41586-022-05172-4)

**Catalogues**
- *Tilings Encyclopedia* — [tilings.math.uni-bielefeld.de](https://tilings.math.uni-bielefeld.de/)
- Gähler, Kwan, Maloney, *A Computer Search for Planar Substitution Tilings with n-Fold Rotational Symmetry* — [arXiv:1404.5193](https://arxiv.org/abs/1404.5193)

---

## Relevance to our shadow / strict-extension approach

The literature *validates the project's premise and tells us where to point the agent.* Mapping findings onto APPROACH.md / CERTIFICATE.md:

**(a) The "projection from a higher layer" frame is established mathematics, not metaphor — use it literally.**
Cut-and-project model sets *are* irrational-slope down-projections of an ℝⁿ lattice (§4.2), and **projection ⇔ substitution are dual descriptions of the same pure-point-diffractive objects** glued by **Pisot numbers** (§4.3). This *is* APPROACH.md's "two charts" and `F41`. So our non-descending object `U` = irrational slope = Pisot inflation factor is a real, well-studied invariant, and CERTIFICATE.md field 4's "rational trace/norm/char-poly, irrational Pisot leading eigenvalue" is exactly the standard algebra of substitution matrices. **Action: build the descent audit on top of model-set/Pisot machinery from Baake–Grimm; do not reinvent it.**

**(b) Novelty is *most reachable* in three open settings — ranked.**
1. **Strongly aperiodic *convex* monotile in the hyperbolic plane ℍ²** — the best-defined open existence question (confirmed open mid-2026, Maiti §3.2). ℍ² is *natively* a "non-Euclidean projection" setting and has rich lattice/Fuchsian-group structure to project from, fitting a higher-layer attack better than flat ℝ². **Highest-value target.**
2. **Strongly aperiodic 3D monotile** — SCD is only weakly aperiodic (screw symmetry); killing the infinite-cyclic symmetry is open (§3.3). A higher-dimensional lattice projecting to a 3-space is the canonical cut-and-project move; the obstruction (screw = `U` descending to a residual cyclic symmetry) is *exactly* a non-descent failure our certificate is built to detect.
3. **Group-theoretic / subshift monotiles on non-abelian or hyperbolic groups** (§3.4) — Coulbois et al. already unify hat + Greenfeld–Tao here; this is where "the same higher layer, two charts" is being actively formalized and where a *new* aperiodic group-monotile is plausibly within reach.
The flat-Euclidean headline is closed, so chasing a *new* planar undecorated monotile is the wrong target; the residual planar questions (uniqueness of tiling class, §3.1) are the only flat openings left.

**(c) The certificate maps onto existing rigorous tools — reuse them as the audit, not the search.**
- **Field 1 (saturation / kill periodic candidates):** Kaplan's **SAT isohedral-tiling / Heesch encodings** (§1.3) and **Jeandel–Rao-style exhaustive enumeration** (§2.1) are exactly "no periodic candidate ≤ size N passes," as a finite, Lean-checkable computation. **Adopt CryptoMiniSat / splr encodings directly for field 1 and field 6.**
- **Fields T1/T2 (spectral drive + stacking across inflation levels):** these *are* RG statements — the **renormalization cocycle / Perron-eigenvalue contraction** of Mazáč 2025 and Baake–Gähler–Mañibo (§4.1) is the literature home for T1; "strict at every inflation level" is RG-tower stability for T2. **Borrow the renormalization-cocycle formalism to state T1/T2 rigorously.**
- **The undecidability results (§2.2) are the *reason* the project's architecture is right:** general "find a tile that tiles only aperiodically" is **undecidable**, so a blind planar search cannot be complete — vindicating APPROACH.md's rejection of the old mutate-and-recheck engine. Work upstairs where the object is *forced*; let a *decidable finite audit* (SAT patch-check + eigenvalue verification) carry the load-bearing step. This is also why CERTIFICATE.md can claim an **unconditional** landing: the audit is finite/decidable even though the ambient existence problem is not.

**(d) Methodologically, the winning recipe is exactly "heuristic walk + exact verifier."**
The hat itself was found by **human intuition + computer audit**; AlphaTensor and TilinGNN (§4.4) show **neural-guided search + exact certificate** discovering provably-correct objects in huge discrete spaces. That is structurally our **agent (heuristic walk of theory space) + SAU six-field certificate (decidable audit)**. The agent should *walk the substitution/projection charts* (candidate lattice/window/slope, or candidate Pisot inflation factor), and the audit should be a SAT/eigenvalue finite check — *not* a shape-space mutation loop.

**(e) Concrete first moves for the agent.**
1. **Enumerate the realized layers**: scrape the **Tilings Encyclopedia** + Gähler–Kwan–Maloney generator (§5) for `(inflation factor, symmetry, dimension)` triples already realized as monotile shadows — the complement is the search space for "not yet realized as a single-prototile shadow."
2. **Target ℍ²**: instantiate the cut-and-project / substitution chart over a Fuchsian/hyperbolic lattice; the open *strongly-aperiodic-convex-monotile* question is the forced higher-layer question to translate down.
3. **Wire the audit**: reuse Kaplan's SAT isohedral encoding (field 1/6) + substitution-matrix Perron/Pisot verification (field 4) + the renormalization cocycle (T1/T2) as the Lean-checkable descent audit.
4. **Borrow the SCD obstruction as a test oracle** for the non-descent field 3 (screw symmetry = `U` half-descending) when working in 3D.
