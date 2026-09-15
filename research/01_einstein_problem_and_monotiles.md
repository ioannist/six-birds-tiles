# The Aperiodic Tiling Problem and Known Aperiodic Protosets / Monotiles

*Research note for the "down-shadow / strict-extension" approach to discovering a new aperiodic monotile. Compiled June 2026 from primary sources (arXiv papers, Wikipedia, expert pages). All URLs cited inline.*

---

## 1. Overview

A **tiling** of the plane covers it with copies of tiles, no gaps and no overlaps. A tiling is **periodic** if it is invariant under two linearly independent translations (it has a lattice of translational symmetries); otherwise it is **non-periodic**. A set of prototiles (a "protoset") is **aperiodic** if it admits tilings of the plane but **only non-periodic ones** — there is no way to use the tiles to make a periodic pattern. ([Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling))

The **einstein problem** (a pun on German *ein Stein*, "one stone") asks for a **single** aperiodic prototile — one shape that tiles the plane but never periodically. This is the holy grail: an "aperiodic monotile." ([Einstein problem — Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem))

Two technical refinements matter:
- **Weakly vs strongly aperiodic.** A tiling/tile is *strongly aperiodic* if it admits no infinite cyclic group of Euclidean motions as symmetries; *weakly aperiodic* if it forbids translational lattices but may still admit, e.g., screw symmetries (irrational rotation + translation). The Schmitt–Conway–Danzer 3D tile (1988–90s) is only *weakly* aperiodic. ([Einstein problem — Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem))
- **"Monotile" with vs without auxiliary matching rules.** Many candidate "single tiles" only tile aperiodically if you *additionally impose decorations / matching rules*, or if the tile is allowed to be disconnected, or if tiles may overlap. A *true* aperiodic monotile forces aperiodicity **by its geometry alone**, as a connected topological disc, with the usual freedom of rotations (and possibly reflections). The 2023 **hat** is the first such tile. ([cs.uwaterloo.ca/~csk/hat/](https://cs.uwaterloo.ca/~csk/hat/))

Why anyone cares: aperiodic tilings are the mathematical models of **quasicrystals**, discovered physically by Dan Shechtman in 1982 (Nobel Prize in Chemistry 2011). Long-range order without periodicity is exactly what these tilings capture. ([Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling))

---

## 2. Timeline / Milestones

| Year | Who | Result | # tiles |
|------|-----|--------|---------|
| 1961 | **Hao Wang** | Posed the *Domino Problem*: is it decidable whether a set of edge-colored square ("Wang") tiles tiles the plane? Conjectured "no aperiodic sets exist" (the *Wang/Fundamental Conjecture*). | — |
| 1964 | **Robert Berger** | Disproved Wang's conjecture: built an aperiodic Wang set and used it to prove the Domino Problem is **undecidable**. First aperiodic protoset. | **20,426** |
| later | Berger; **Donald Knuth** | Reductions of Berger's set. | 104; 92 |
| 1966/68 | **Hans Läuchli** | Smaller aperiodic Wang set (published later). | 40 |
| 1971 | **Raphael M. Robinson** | Famous aperiodic set of 6 square (notched) tiles enforcing a hierarchical "Robinson pattern"; clean undecidability proof. | **6** |
| 1973–74 | **Roger Penrose** | P1 (pentagons etc.), P2 (**kites & darts**), P3 (**two rhombi**); reduced the count to **2** tiles with matching rules; 5-fold symmetric, self-similar (golden-ratio inflation). | **2** |
| 1977 | **Robert Ammann** | Independently found several aperiodic sets; "Ammann bars" (decoration lines) and Ammann–Beenker (8-fold) tiling. | 2+ |
| 1981 | **N. G. de Bruijn** | *Cut-and-project* / "pentagrid" construction of Penrose tilings as projections of a 5D cubic lattice — the projection viewpoint. | — |
| 1982 | **Shechtman** (physics) | Quasicrystals discovered experimentally — physical realization of aperiodic order. | — |
| 1996 | **Petra Gummelt** | A single decorated decagon that tiles aperiodically — but **only by allowing overlaps**, so not a true tiling monotile. | "1" (overlaps) |
| ~1996 | **Penrose** | "(1+ε+ε²)" functional monotile — effectively one shape but uses tiny auxiliary tiles / hierarchical hexagon rules. | "≈1" |
| 2010 | **Joan Taylor & Joshua Socolar** | **Socolar–Taylor tile**: a single hexagonal prototile with matching rules (or, undecorated, a *disconnected* tile) that is aperiodic. The closest pre-2023 "monotile," but a true single connected tile under geometry alone remained open. | "1" (marked / disconnected) |
| 2013 | **Jeandel–Rao** (announced; pub. 2021) | Proved the **minimum** aperiodic *Wang* set has exactly **11** tiles (with 4 colors), by exhaustive computer search. | **11** (optimal) |
| **2022 Nov** | **David Smith** | Discovered the **hat** (a 13-gon / 8-kite polykite) experimentally; suspected it was the einstein. | **1** |
| **2023 Mar** | **Smith, Myers, Kaplan, Goodman-Strauss** | *"An aperiodic monotile"* — proved the **hat** is a true aperiodic monotile (using rotations **and reflections**). 60-year search resolved. | **1** |
| **2023 May** | same four | *"A chiral aperiodic monotile"* — the **Spectre** (from Tile(1,1)): a *strictly chiral* monotile that tiles aperiodically with **rotations & translations only — no reflections**. | **1** |
| 2022–23 | **Greenfeld & Tao** (separate result) | Counterexample to the **periodic tiling conjecture** in high dimensions: a single tile that tiles ℤ^d / ℝ^d by **translations only** but never periodically. *Different problem* (high-dim, translations-only) — not the planar einstein. | 1 (high-d) |

Sources for this timeline: [Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling); [Einstein problem — Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem); survey [*Planar aperiodic tile sets: from Wang tiles to the Hat and Spectre monotiles*, arXiv:2310.06759](https://arxiv.org/html/2310.06759v2); [Penrose tiling — Wikipedia](https://en.wikipedia.org/wiki/Penrose_tiling).

---

## 3. Precise descriptions of the key protosets

### 3.1 Wang tiles (1961) and Berger's undecidability (1964)
**Wang tiles** are unit squares with colored edges; they may be placed by **translation only** (no rotation/reflection), and adjacent edges must share a color. Wang noticed that *if* every tileable set tiled periodically, the Domino Problem would be decidable, and conjectured this. **Berger (1964)** built an aperiodic set (20,426 tiles), reducing the **Halting Problem** to tiling, thereby proving the Domino Problem **undecidable** — and, as a byproduct, that **aperiodic sets exist**. Undecidability is the deep reason small aperiodic sets are hard to find: there's no general algorithm to decide tileability. ([arXiv:2310.06759](https://arxiv.org/html/2310.06759v2))

The minimal Wang set is now known: **Jeandel & Rao** proved **11 tiles / 4 colors** is optimal by computer search. ([arXiv:2310.06759](https://arxiv.org/html/2310.06759v2))

### 3.2 Robinson tiles (1971)
Six square tiles with bumps/notches whose matching rules **force** a hierarchy of nested squares (the "Robinson pattern"): squares of side 2, 4, 8, … at every scale. Because the hierarchy exists at *all* scales, no translation can map the tiling to itself → non-periodic. This **hierarchical / substitution forcing** is the template that the hat proof later reuses combinatorially. ([Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling))

### 3.3 Penrose tilings P1 / P2 / P3 (1973–74)
- **P1**: original set (pentagons, pentagram, "boat," diamond).
- **P2**: **kites and darts** (two quadrilaterals from a rhombus), with arc/colour matching rules.
- **P3**: **two rhombi** (a "thick" 72°/108° and a "thin" 36°/144°), matching rules via edge decorations / Ammann bars.

All are mutually locally derivable, have global **5-fold** statistical symmetry, and are **self-similar**: a *substitution / inflation* replaces each tile by a scaled cluster, with linear inflation factor the **golden ratio** φ = (1+√5)/2. φ is a **Pisot number**, which is exactly why Penrose tilings have a **pure-point diffraction spectrum** (sharp Bragg peaks). The matching rules can be re-encoded as geometric **bumps and dents**, giving genuine *jigsaw* tiles. But Penrose still needs **two** distinct shapes. ([Penrose tiling — Wikipedia](https://en.wikipedia.org/wiki/Penrose_tiling); [Tilings Encyclopedia: Inflation factor](https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/))

Key general theorem (Goodman-Strauss, 1998): **any** substitution tiling satisfying a mild condition can be enforced by local matching rules — substitution structure ⇒ matching rules. This is the formal bridge between "hierarchical/inflation layer" and "local matching layer." ([Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling))

### 3.4 Ammann (1977)
Robert Ammann found several aperiodic pairs independently of Penrose, including the **Ammann–Beenker** (8-fold, silver-ratio inflation δ = 1+√2, also Pisot) tiling, and introduced **Ammann bars** — lines drawn on tiles that, across a whole tiling, line up into families of parallel lines with a Fibonacci/aperiodic spacing. Ammann bars are a decoration that *exposes* the hidden one-dimensional aperiodic structure — conceptually a low-dimensional "shadow" of the matching constraints, and they reappear in alternative hat-aperiodicity proofs ("Golden Ammann bars"). ([Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling); alternative proof [arXiv:2307.12322](https://arxiv.org/html/2307.12322v5))

### 3.5 Socolar–Taylor tile (2010) — the marked / disconnected "near-monotile"
Joan Taylor (amateur, Tasmania) found the rules in 2010; with Joshua Socolar published *"An aperiodic hexagonal tile"* (J. Combin. Theory Ser. A, 2011). Two equivalent guises:
- **Decorated hexagon** with two matching rules: **(R1)** black stripe lines must continue across tile edges; **(R2)** purple "flags" at vertices of tiles meeting across a single hexagon edge must point the same way. Crucially, R2 constrains tiles that are **not edge-adjacent** (a next-nearest / non-local rule). The forced structure is a Sierpiński-triangle-like hierarchy. It is **strongly aperiodic** in 2D.
- **Undecorated geometric** version: to encode the same rules by shape alone, the tile must be **disconnected** (not simply connected — topologically not a disc). It is *unknown whether* the rule can be realized by a **simply connected** 2D tile. In 3D the connected analog is only **weakly** aperiodic (you can stack non-periodic 2D layers). ([Socolar–Taylor tile — Wikipedia](https://en.wikipedia.org/wiki/Socolar%E2%80%93Taylor_tile); [arXiv:2310.06759](https://arxiv.org/html/2310.06759v2))

So before 2023 the einstein problem was open *precisely* because every "monotile" cheated on one axis: overlaps (Gummelt), auxiliary tiles (Penrose 1+ε), non-local matching rules / disconnection (Socolar–Taylor), or weak aperiodicity (Schmitt–Conway–Danzer).

### 3.6 The hat (2023) — the first true aperiodic monotile
**What it is.** Overlay a **hexagonal grid**; cut each hexagon with three straight lines through midpoints of opposite edges into **6 kites**. The **hat** is the polygon formed by **8 of these kites**, taken from **three neighbouring hexagons**. As a polygon it is a **13-sided** shape ("looks like a hat / fedora; upside-down, a T-shirt"). It is a **polykite** (a polyform made of kites). ([cs.uwaterloo.ca/~csk/hat/](https://cs.uwaterloo.ca/~csk/hat/); [Aperiodical, Mar 2023](https://aperiodical.com/2023/03/an-aperiodic-monotile-exists/))

**The Tile(a,b) continuum.** Smith also found the **turtle** (10 kites). Myers realized hat and turtle are two members of a **one-parameter continuum** of combinatorially identical tiles obtained by varying two edge lengths: **Tile(a, b)** with `a ∈ [0, √3]`, `b ∈ [0, 1]`. Special members ([arXiv:2310.06759](https://arxiv.org/html/2310.06759v2)):
- **Tile(0, 1) = "Comet"** (one degenerate extreme),
- **Tile(√3, 0) = "Chevron"** (other degenerate extreme),
- **Tile(√3, 1) = the Hat**,
- **Tile(1, 1) = the equilateral member** = the *precursor of the Spectre* (originally thought "uninteresting" because *with* its mirror image it tiles periodically).

Generic interior members are aperiodic monotiles; the two degenerate endpoints (Comet, Chevron) tile periodically and are used in the proof (below).

**Reflections.** Every hat tiling necessarily uses **both** the hat and its **mirror image**; the *unreflected : reflected* tile ratio is **φ⁴ : 1** (roughly 1 in 7 tiles is flipped). So the hat is an aperiodic monotile *with reflections allowed*. Whether you could avoid reflections was the immediate open question — answered by the Spectre. ([Aperiodical, Mar 2023](https://aperiodical.com/2023/03/an-aperiodic-monotile-exists/))

### 3.7 The Spectre / Tile(1,1) (2023) — strictly chiral monotile, no reflections
The team revisited **Tile(1,1)** (the equilateral member). They proved it is **weakly chiral**: *if you forbid reflections by fiat*, Tile(1,1) tiles the plane but **only non-periodically**. ([Aperiodical, May 2023](https://aperiodical.com/2023/05/now-thats-what-i-call-an-aperiodic-monotile/))

To upgrade "forbid by fiat" to "forbidden by geometry," they **modify the edges**: replace each straight edge of Tile(1,1) with **any asymmetric curve, consistently oriented**. A reflected copy then simply **cannot interlock** with unreflected copies. The resulting ghost-shaped tile is the **Spectre**, a **strictly chiral aperiodic monotile**: it admits tilings, all tilings are non-periodic, and all use a **single chirality** (no mirror copies) — even when reflections are *permitted*, they never appear. ([Aperiodical, May 2023](https://aperiodical.com/2023/05/now-thats-what-i-call-an-aperiodic-monotile/); paper [arXiv:2305.17743](https://arxiv.org/abs/2305.17743))

This is the strongest possible solution to the einstein problem: one connected tile, rotations and translations only.

---

## 4. The 2023 proof techniques, explained

Both papers prove the same core statement — *the tile admits tilings, and every tiling is non-periodic* — and give **two independent proofs** of non-periodicity. ([cs.uwaterloo.ca/~csk/hat/](https://cs.uwaterloo.ca/~csk/hat/): "we give two different proofs of aperiodicity. One of them relies on a computer-assisted case-based analysis.")

### 4.1 Proof A — combinatorial / hierarchical substitution (computer-assisted)
**Step 1 — Metatiles.** They prove that in *any* legal hat tiling, the tiles partition **uniquely** into four kinds of clusters called **metatiles**, labeled **H, T, P, F** (clusters of 1, 2, or 4 hats; H is the 4-hat cluster with hexagonal symmetry). ([Aperiodical, Mar 2023](https://aperiodical.com/2023/03/an-aperiodic-monotile-exists/): "no matter how you put the tiles down, it will always be possible to divide it up so that each tile belongs to one of a set of four clusters … H, T, P or F.")

**Step 2 — Substitution.** The metatiles obey a **substitution (inflation) rule**: each metatile, scaled up, is composed of smaller metatiles, producing **supertiles**, then super-supertiles, etc. The metatiles "have the same symmetries as the basic tiles," so the rule iterates cleanly. The map is a **recognisable, non-stone substitution** (recognisable = the hierarchy can be uniquely reconstructed from the infinite tiling). ([Aperiodical](https://aperiodical.com/2023/03/an-aperiodic-monotile-exists/); [arXiv:2310.06759](https://arxiv.org/html/2310.06759v2))

**Step 3 — The non-periodicity argument (the crux).** Because the substitution is **recognisable**, every legal tiling decomposes into supertiles **in exactly one way**, at every level of the hierarchy. The survey states it cleanly: *"one can identify structure in the tiling of arbitrarily large size, and hence the tiling cannot be periodic."* ([arXiv:2310.06759](https://arxiv.org/html/2310.06759v2)) The logical force: if a translation `x` were a symmetry, it would have to preserve the **unique** supertile partition at every level; but the supertiles grow without bound, so any fixed `x` is eventually smaller than a supertile and **cannot** map the (uniquely determined) hierarchy onto itself — contradiction. Equivalently, *"if there were a translational symmetry, hierarchies of supertiles could not be unique."* ([An aperiodic monotile, escholarship](https://escholarship.org/uc/item/3317z9z9) / abstract)

This is the heart of the matter and the part most relevant to us (see §6): **a single hierarchical/substitutive layer that is *recognisable* (uniquely liftable) cannot factor through, or be invariant under, the translation group.**

The case analysis showing the metatile decomposition is forced (there are no other ways to legally surround tiles) is the **computer-assisted** part — it enumerates the finite set of possible local configurations ("coronas," the rings of tiles around a tile/cluster) and checks each. "Fault lines" arguments (showing the tiling has no infinite straight cut separating two periodic half-planes) are part of ruling out periodicity directly.

### 4.2 Proof B — geometric incommensurability (the "Comet/Chevron" argument)
This proof uses the **Tile(a,b) continuum**. Idea ([arXiv:2310.06759](https://arxiv.org/html/2310.06759v2)):
1. All members Tile(a,b) are **combinatorially equivalent** — a tiling by one yields a "tiling" by any other (same adjacency graph, edges re-scaled).
2. The two **degenerate** endpoints, the **Comet** Tile(0,1) and the **Chevron** Tile(√3,0), tile **periodically**.
3. **Suppose** a hat (or generic Tile(a,b)) tiling were periodic. Then via the combinatorial equivalence the **Comet tiling and the Chevron tiling derived from it would both be periodic with related lattices**, forcing an **affine map between the Comet's lattice and the Chevron's lattice**.
4. That affine map would force an algebraic relation that **cannot hold** because it mixes **√3 and 1** incommensurably — *"an argument somewhat similar to the proof that √2 is irrational."* Contradiction ⇒ the generic tile is **non-periodic**.

So Proof B is a genuine *metric/number-theoretic* incommensurability obstruction (lengths in ratio involving √3 cannot close up into a common lattice), independent of the combinatorial hierarchy.

### 4.3 The Spectre proof
For the Spectre, the analogous proof is a **hierarchical substitution system on nine hexagonal "metatiles"** (Simon Tatham's exposition labels them G, D, J, L, X, P, S, F, Y; original Greek Γ Δ Θ Λ Ξ Π Σ Φ Ψ). The expansion turns each hexagon into a cluster of **7 or 8** hexagons; the **G** hex carries **two** Spectres, and an **S/"Mystic"** configuration needs special edge handling. Recognizability of this substitution again forces unique hierarchical decomposition ⇒ non-periodicity, and the consistent edge-orientation forbids reflected copies ⇒ strict chirality. ([Simon Tatham, *Combinatorial coordinates for the aperiodic Spectre tiling*](https://www.chiark.greenend.org.uk/~sgtatham/quasiblog/aperiodic-spectre/); [arXiv:2305.17743](https://arxiv.org/abs/2305.17743))

### 4.4 Inflation factor / eigenvalue (the spectral audit)
The follow-up dynamical-systems analysis (**Baake, Gähler, Sadun**, *Dynamics and topology of the Hat family of tilings*) pins down the inflation arithmetic. They build a self-similar member ("**CAP** tiling") of the hat family with an **exact stone inflation**; its substitution acts on cohomology `H¹` with **eigenvalues λ = φ^±²**, where φ=(1+√5)/2. The **geometric (linear) inflation factor is φ² = (3+√5)/2 ≈ 2.618**, and **φ² is a Pisot (Pisot–Vijayaraghavan) number**. Consequently the tiling has **pure-point dynamical/diffraction spectrum**. ([arXiv:2305.05639](https://arxiv.org/html/2305.05639v3))

> A self-similar inflation tiling has a non-trivial **pure-point** spectral component **iff** the inflation scaling factor is a **Pisot number**. ([Tilings Encyclopedia / standard Meyer–Pisot theory](https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/))

(Note: φ² should not be confused with the **φ⁴** that appears as the *ratio of unreflected to reflected hats* — a different quantity.)

### 4.5 The projection / cut-and-project structure (most important for us)
The same Baake–Gähler–Sadun paper proves the hat is literally a **projected shadow** of a higher periodic/model-set structure:
- The self-similar **CAP** tiling is **MLD** (mutually locally derivable) to a **Euclidean cut-and-project set / model set**, with **2-dimensional internal (perp) space**.
- **Theorem:** *"the Hat tiling is a reprojection of the CAP tiling, as is every other member of the Hat family"* (after choosing scale & orientation). More precisely: *"Every tiling … topologically conjugate to the CAP tiling is MLD to a cut-and-project set with the same total space and acceptance domain … only with a different projection."* ([arXiv:2305.05639](https://arxiv.org/html/2305.05639v3))
- The **Spectre** family likewise comes from a **4→2 dimensional cut-and-project scheme** with windows of **Rauzy-fractal** type, and has pure-point spectrum. ([arXiv:2502.03268 *Diffraction of the Hat and Spectre tilings*](https://arxiv.org/html/2502.03268v1); [arXiv:2411.15503 *On the long-range order of the Spectre tilings*](https://arxiv.org/abs/2411.15503))

In other words, the hat/spectre tilings are *down-shadows of a lawful higher-dimensional lattice* — exactly the picture our project is built on (see §6).

---

## 5. How the hat was actually discovered

- **David Smith** — amateur mathematician, **retired print technician**, from **Bridlington, East Yorkshire**. Not a professional academic. ([David Smith — Wikipedia](https://en.wikipedia.org/wiki/David_Smith_(amateur_mathematician)))
- **Nov 2022:** While playing with shapes in the **PolyForm Puzzle Solver** software, Smith found a **13-sided polygon** (the hat). He then cut **cardboard copies by hand** and noticed it seemed to tile the plane *without ever settling into a repeating pattern*. ([David Smith — Wikipedia](https://en.wikipedia.org/wiki/David_Smith_(amateur_mathematician)))
- Smith emailed **Craig S. Kaplan** (computer scientist, University of Waterloo), who tested it with his own **Heesch-number / tiling software** and confirmed it kept tiling outward with no periodicity. They nicknamed it **"the hat."** Smith then found a second shape, the **"turtle."** ([cs.uwaterloo.ca/~csk/hat/](https://cs.uwaterloo.ca/~csk/hat/); [arXiv:2310.06759](https://arxiv.org/html/2310.06759v2))
- **mid-Jan 2023:** Kaplan brought in **Joseph Samuel Myers** (Cambridge; expert software developer / combinatorialist) and **Chaim Goodman-Strauss** (then U. Arkansas; tiling theorist, now also at the National Museum of Mathematics). **Myers** discovered that the hat and turtle are members of the **same Tile(a,b) continuum** and supplied the **computer-assisted combinatorial-substitution proof**; **Goodman-Strauss** contributed the substitution/hierarchical framework and exposition. ([David Smith — Wikipedia](https://en.wikipedia.org/wiki/David_Smith_(amateur_mathematician)); [Waterloo News](https://uwaterloo.ca/news/mathematics/trick-hat))
- **20 Mar 2023:** preprint *"An aperiodic monotile"* posted (arXiv:2303.10798).
- **May 2023:** Smith's observation about the **equilateral Tile(1,1)** led to the **Spectre**; preprint *"A chiral aperiodic monotile"* (arXiv:2305.17743) posted 28 May 2023.
- Both papers published in **Combinatorial Theory**, 2024 (the hat in 4(1), the Spectre in 4(2)). ([momath.org/the-hat](https://momath.org/the-hat/))

Goodman-Strauss likened Smith's find to *"catching a never-before-seen animal in the wild,"* and noted a professional under publication pressure would have been "foolish" to attempt such an open-ended search — a nod to the value of the amateur/exploratory route. ([Univ. of Cambridge, "A tip of the hat"](https://www.maths.cam.ac.uk/features/tip-hat-celebrating-aperiodic-monotile-discovery))

---

## 6. Open problems and the frontier

- **Are there *other* essentially-different aperiodic monotiles?** Unknown. The hat/spectre and their Tile(a,b) continuum are one family; whether there exist combinatorially *inequivalent* single-tile solutions is open. ([arXiv:2310.06759](https://arxiv.org/html/2310.06759v2))
- **Non-polygonal monotiles?** The Spectre already uses **curved** edges, but the question of smooth/fractal-boundary monotiles, or a classification of *which* edge modifications preserve strict chirality, is open.
- **Simply-connected Socolar–Taylor?** Still **unknown** whether the Socolar–Taylor matching rule can be realized by a **simply connected** undecorated 2D tile. ([Socolar–Taylor — Wikipedia](https://en.wikipedia.org/wiki/Socolar%E2%80%93Taylor_tile))
- **Higher dimensions / other geometries.** "Einstein" tiles in hyperbolic space, in 3D (beyond weakly-aperiodic Schmitt–Conway–Danzer), and the **Greenfeld–Tao** translations-only counterexample to the periodic tiling conjecture (high-dimensional ℤ^d) chart a *different* frontier where the tools are group-theoretic rather than Euclidean-geometric. ([arXiv:2211.15847](https://arxiv.org/abs/2211.15847); [Quanta](https://www.quantamagazine.org/nasty-geometry-breaks-decades-old-tiling-conjecture-20221215/))
- **Algebra/groups viewpoint.** Recent work *"Aperiodic monotiles: from geometry to groups"* (arXiv:2409.15880) recasts the hat via group theory, hinting at systematic search machinery for new monotiles. ([arXiv:2409.15880](https://arxiv.org/abs/2409.15880))
- **Spectral / physical frontier.** Diffraction, the dynamical hull, the model-set / Rauzy-window description, and physics on hat/spectre tilings (Ising, dimer, elasticity) are active. ([arXiv:2502.03268](https://arxiv.org/html/2502.03268v1); [arXiv:2411.15503](https://arxiv.org/abs/2411.15503))

---

## 7. Authoritative sources (titles + URLs)

**Primary papers**
- Smith, Myers, Kaplan, Goodman-Strauss, *An aperiodic monotile*, Combinatorial Theory 4(1), 2024 — arXiv:2303.10798. https://arxiv.org/abs/2303.10798 · eScholarship copy: https://escholarship.org/uc/item/3317z9z9 · author PDF: https://strauss.hosted.uark.edu/distribution/papers/einstein.pdf
- Smith, Myers, Kaplan, Goodman-Strauss, *A chiral aperiodic monotile*, Combinatorial Theory 4(2), 2024 — arXiv:2305.17743. https://arxiv.org/abs/2305.17743 · author PDF: https://strauss.hosted.uark.edu/distribution/papers/spectre.pdf
- Socolar & Taylor, *An aperiodic hexagonal tile*, J. Combin. Theory Ser. A (2011). (See Wikipedia summary below.)
- Greenfeld & Tao, *A counterexample to the periodic tiling conjecture* — arXiv:2211.15847 (Annals of Math, 2024). https://arxiv.org/abs/2211.15847

**Spectral / projection / dynamics (key for our approach)**
- Baake, Gähler, Sadun, *Dynamics and topology of the Hat family of tilings* — arXiv:2305.05639. https://arxiv.org/html/2305.05639v3
- *Diffraction of the Hat and Spectre tilings and some of their relatives* — arXiv:2502.03268. https://arxiv.org/html/2502.03268v1
- *On the long-range order of the Spectre tilings* — arXiv:2411.15503. https://arxiv.org/abs/2411.15503
- Tilings Encyclopedia, *Inflation factor* (Perron–Frobenius / Pisot ⇔ pure-point). https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/

**Surveys, expositions, project pages**
- *Planar aperiodic tile sets: from Wang tiles to the Hat and Spectre monotiles* — arXiv:2310.06759. https://arxiv.org/html/2310.06759v2
- *Aperiodic monotiles: from geometry to groups* — arXiv:2409.15880. https://arxiv.org/abs/2409.15880
- Craig Kaplan, hat project page (interactive). https://cs.uwaterloo.ca/~csk/hat/
- Simon Tatham, *Combinatorial coordinates for the aperiodic Spectre tiling*. https://www.chiark.greenend.org.uk/~sgtatham/quasiblog/aperiodic-spectre/
- The Aperiodical, *An aperiodic monotile exists!* (Mar 2023). https://aperiodical.com/2023/03/an-aperiodic-monotile-exists/
- The Aperiodical, *Now that's what I call an aperiodic monotile!* (Spectre, May 2023). https://aperiodical.com/2023/05/now-thats-what-i-call-an-aperiodic-monotile/
- National Museum of Mathematics, *The Hat and the Spectre*. https://momath.org/the-hat/
- Univ. of Cambridge, *A tip of the hat: celebrating the aperiodic monotile discovery*. https://www.maths.cam.ac.uk/features/tip-hat-celebrating-aperiodic-monotile-discovery
- Univ. of Waterloo News, *A trick of the hat*. https://uwaterloo.ca/news/mathematics/trick-hat

**Reference encyclopedias**
- Wikipedia: *Aperiodic tiling* https://en.wikipedia.org/wiki/Aperiodic_tiling · *Einstein problem* https://en.wikipedia.org/wiki/Einstein_problem · *Penrose tiling* https://en.wikipedia.org/wiki/Penrose_tiling · *Socolar–Taylor tile* https://en.wikipedia.org/wiki/Socolar%E2%80%93Taylor_tile · *David Smith (amateur mathematician)* https://en.wikipedia.org/wiki/David_Smith_(amateur_mathematician)

---

## Relevance to our shadow / strict-extension approach

Our strategy is to treat an aperiodic tiling as the **down-shadow (projection)** of a higher, **lawful (periodic) layer**, and to certify aperiodicity as a **strict extension / non-factorization** (the hierarchical layer doesn't factor through the local matching layer), auditing the inflation factor (a **Pisot** number) as an **eigenvalue**. The 2023 results and their follow-ups map onto this picture remarkably directly:

1. **The "shadow / projection" is not a metaphor — it is a theorem for the hat.** Baake–Gähler–Sadun prove the hat (and *every* member of the family) is a **reprojection of the self-similar CAP tiling**, which is **MLD to a Euclidean cut-and-project model set** with a 2-dimensional internal space. ([arXiv:2305.05639](https://arxiv.org/html/2305.05639v3)) So there *already exists* a "higher lawful layer" (the lattice in total space `physical ⊕ internal`) whose **orthogonal projection / window-selection** is the hat tiling. The Spectre is the same with a Rauzy-fractal window (4→2 scheme). Our project should regard the **cut-and-project total space + acceptance window** as the explicit "upper layer," and our candidate monotile as a **section/shadow** of it. The hat is an existence proof that this architecture can yield a *connected single tile*.

2. **The inflation factor *is* the eigenvalue audit, and it is Pisot.** The substitution acts on cohomology with eigenvalues **φ^±²**; the linear inflation is **φ² (Pisot)**; and Pisot-ness is *exactly* the spectral certificate that the projection has **pure-point** diffraction (genuine long-range order). ([arXiv:2305.05639](https://arxiv.org/html/2305.05639v3); [Tilings Encyclopedia](https://tilings.math.uni-bielefeld.de/glossary/inflation-factor/)) For us this means: the **largest eigenvalue of our substitution matrix** (Perron–Frobenius) must be a Pisot number — that single algebraic condition is the "eigenvalue audit" certifying that the down-shadow is a quasicrystal and not noise. If our proposed higher layer yields a non-Pisot expansion, the shadow will *not* have pure-point order — a fast falsification test.

3. **Non-factorization = recognizability of the substitution = the actual aperiodicity proof.** The hat's **Proof A** is precisely a non-factorization statement: the **recognisable** (uniquely liftable) hierarchical/substitution structure means each tiling decomposes into supertiles in **exactly one way at every scale**, so **no translation can be a symmetry** ("if there were translational symmetry, the hierarchy of supertiles could not be unique"). ([escholarship](https://escholarship.org/uc/item/3317z9z9); [arXiv:2310.06759](https://arxiv.org/html/2310.06759v2)) In our language: the **hierarchical (substitution) layer is a *strict* extension of the local (matching/corona) layer — it does not factor through the translation group**. This is the template to formalize: prove that the lift to the upper layer is **injective/recognisable**, and aperiodicity follows because a periodic shadow would force the lift to be translation-invariant, contradicting recognizability. The **finite corona case-analysis** (computer-assisted) is the concrete mechanism that establishes recognizability — our certification should produce an analogous finite, machine-checkable corona/atlas argument.

4. **Two independent certificates — combinatorial *and* metric.** The hat has Proof A (combinatorial/hierarchical non-factorization) **and** Proof B (geometric **incommensurability**: lengths in ratio √3 : 1 cannot close into a common lattice — "like √2 irrational"). For robustness our framework should likewise aim for a **two-pronged certificate**: (a) a *non-factorization/recognizability* proof (the hierarchical layer is a strict extension), and (b) a *number-theoretic incommensurability* obstruction tied to the projection geometry (irrational/Pisot length ratios in the window). The fact that the **degenerate endpoints** (Comet, Chevron) *do* tile periodically is instructive: it shows aperiodicity is a **generic, open-condition** property of the projection parameters, lost only on a measure-zero degenerate set — our search should expect aperiodicity to be the rule, with periodic shadows occurring exactly where the upper layer's projection parameters become commensurate.

5. **The matching-layer ↔ hierarchy-layer bridge already has a theorem.** Goodman-Strauss's result — any (mild) **substitution tiling can be enforced by local matching rules** — is the formal link between our "higher lawful layer" (substitution/inflation) and the "local matching layer" (coronas). Our **strict-extension / non-factorization** claim is the *converse-flavored* statement we must establish: that the matching layer alone does **not** recover periodicity, i.e. the hierarchy is **strictly more** than what local rules permit to be periodic. The hat is the proof of concept that this gap can be realized by **one connected tile with geometry alone**. ([Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling))

**Bottom line for the project.** The hat/spectre program supplies a ready-made, theorem-backed instance of our entire architecture: *higher periodic lattice in (physical ⊕ internal) space → cut-and-project shadow → recognisable substitution whose Perron eigenvalue is the Pisot inflation φ² → aperiodicity certified because the recognisable hierarchy cannot factor through translations.* To "discover a NEW essentially-different monotile" we should look for a **different upper lattice / window / Pisot inflation** whose shadow is connected and single-tile, and whose recognizability (non-factorization) we can certify by a finite corona atlas plus an incommensurability/eigenvalue audit. Replacing φ² with another Pisot unit (e.g. the plastic number, the silver ratio 1+√2 of Ammann–Beenker, or a cubic Pisot) is the natural first axis of search.
