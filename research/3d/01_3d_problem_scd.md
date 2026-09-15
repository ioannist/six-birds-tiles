# The 3D aperiodic-monotile problem and Schmitt–Conway–Danzer (SCD)

*Focused 3D deep-dive for the "down-shadow / strict-extension" approach. Compiled June 2026 from primary sources (arXiv, Baake–Frettlöh, Baake–Grimm, Socolar–Taylor, Kaplan, Wikipedia). All URLs cited inline. PROVEN vs OPEN flagged with dates; recent claims marked and verified where possible.*

Read [`../README.md`](../README.md) (the seven planar pillars) and [`../01_einstein_problem_and_monotiles.md`](../01_einstein_problem_and_monotiles.md) first — this doc assumes the planar vocabulary (cut-and-project, recognizability, Pisot inflation, hull = inverse limit, non-factorization).

---

## 1. Overview — the question, and why 3D is genuinely different

The **einstein problem** asks for a single prototile that admits tilings of a space but **only non-periodic** ones. In the Euclidean **plane** this was settled in 2023: the **hat** (with reflections) and the **spectre** (chiral, rotations+translations only) are true aperiodic monotiles ([Smith–Myers–Kaplan–Goodman-Strauss 2023, arXiv:2303.10798](https://arxiv.org/abs/2303.10798); [chiral, arXiv:2305.17743](https://arxiv.org/abs/2305.17743); published *Combinatorial Theory*, July 2024).

In **three dimensions** the situation is older, subtler, and *not* resolved in the same sense:

- **PROVEN (1988–94):** a single **convex** polyhedron — the **Schmitt–Conway–Danzer (SCD) tile** — tiles ℝ³ with **no translational symmetry whatsoever**. So a *convex weakly-aperiodic monotile exists in 3D*. This is striking because in 2D a convex aperiodic monotile is **impossible** (see §4).
- **THE CATCH:** every SCD tiling still carries an **infinite screw symmetry** (a rotation by an irrational angle composed with a lift). It is therefore only **weakly** aperiodic, not **strongly** aperiodic. The non-periodicity is also "not mysterious": it is visibly 2D-periodic layers stacked with a twist ([Socolar–Taylor 2011, arXiv:1009.1419](https://arxiv.org/abs/1009.1419); [Kaplan 2025, arXiv:2509.12216](https://arxiv.org/pdf/2509.12216)).
- **OPEN (as of June 2026):** does a **strongly aperiodic monotile** exist in Euclidean 3-space — one whose tilings admit **no infinite cyclic group of isometries** at all? Convex or not, with or without matching rules, this is unresolved. Kaplan (2025): *"Many of the ideas and algorithms we used to prove the hat's aperiodicity could be adapted to work in 3D space, but personally I am daunted by the prospect of deducing the behaviour of any candidate shapes that might be discovered there."* ([arXiv:2509.12216](https://arxiv.org/pdf/2509.12216), §"higher dimensions").

The phrase **"both an existence proof and a cautionary tale about the definition of aperiodicity in 3D"** (Kaplan, ibid.) is the cleanest one-line summary of SCD's role.

Why anyone cares: aperiodic tilings model **quasicrystals** (Shechtman, Nobel 2011). But note a payload-relevant subtlety established below — SCD is **not** a model set: its diffraction is **singular continuous**, not pure-point ([Baake–Frettlöh 2004, arXiv:math-ph/0411052](https://arxiv.org/abs/math-ph/0411052)). That is exactly the fingerprint of the screw degree of freedom and is central to §8.

---

## 2. The SCD tile — exact construction and history

### 2.1 History
- **1988 — Peter Schmitt** found a single aperiodic prototile in ℝ³. *"While no tiling by this prototile admits a translation as a symmetry, some have a screw symmetry"* ([Einstein problem — Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem)). Schmitt's original tile was **non-convex**.
- **early 1990s — John H. Conway and Ludwig Danzer** independently elaborated it; **they modified Schmitt's prototile into a convex one** — the **biprism**. The combined object is the **Schmitt–Conway–Danzer (SCD) tile**, sometimes "Conway's biprism." Conway's own writeup is archived at [The Geometry Junkyard: *Conway on his aperiodic biprism*](https://ics.uci.edu/~eppstein/junkyard/biprism.html) (D. Eppstein). Danzer's version restricts the inter-layer shifts to a discrete set to make it crystallographically usable ([Baake–Frettlöh 2004](https://arxiv.org/abs/math-ph/0411052), §1, ref. [7] = Senechal's *Quasicrystals and Geometry*).

### 2.2 The polyhedron (exact)
The SCD tile is **combinatorially equivalent to the gyrobifastigium** (Johnson solid J₂₆: two triangular prisms glued so their top edges are perpendicular), but **"made generic"** — the regular faces become **parallelograms and irregular triangles**, with equalities between sides/angles deliberately avoided ([Gyrobifastigium / SCD prototile — Wikipedia](https://en.wikipedia.org/wiki/Gyrobifastigium); [Polytope Wiki: SCD biprism](https://polytope.miraheze.org/wiki/Schmitt%E2%80%93Conway%E2%80%93Danzer_biprism)). It has **8 faces = 4 triangles + 4 parallelograms**.

**Exact coordinates** (the classical construction, [Baake–Frettlöh 2004, §1](https://arxiv.org/abs/math-ph/0411052)). Choose `0 < λ < 1` and positive reals `b₁, b₂, c`. Set

- `φ = arctan(b₁/b₂)`,  `a = √(b₁² + b₂²)`,
- **a** = (a, 0, 0), **b** = (b₁, b₂, 0), **c** = λ**b** + (0,0,c), **d** = λ**a** − (0,0,c).

Then the SCD tile is the convex hull
```
T = conv( 0, a, b, a+b,  c, a+c,  d, b+d ).
```
This is the **union of two triangular prisms**, conv(0, a, b, a+b, c, a+c) and conv(0, a, b, a+b, d, b+d), **glued along the rhombic facet** conv(0, a, b, a+b) — hence *biprism*. The tile is called **incommensurate** (the interesting case) when **φ ∉ πℚ**, i.e. the prism-tilt angle is an irrational multiple of π; **commensurate** otherwise.

The single tunable angle φ (and the gluing that makes the two prisms' ridge directions non-parallel) is the entire source of aperiodicity.

---

## 3. Why SCD tiles only non-periodically — and why only *weakly*

This is the heart of the matter; the mechanism is completely explicit ([Baake–Frettlöh 2004, §1](https://arxiv.org/abs/math-ph/0411052); [Socolar–Taylor 2011, §"SCD"](https://arxiv.org/abs/1009.1419)).

**Step 1 — forced layers.** Translated copies of T can only mate by joining their **triangular facets** (the top of one prism plugs the valley of the next). Joining triangular facet conv(0,b,c)↔conv(a,a+b,a+c) and conv(0,a,d)↔conv(b,a+b,b+d) and continuing until no triangular facet is exposed, you are **forced** to build a single flat **2D-periodic layer** `L = Γ + T`, where `Γ = ℤa + ℤb` is a planar lattice. The **top** of L is a system of parallel ridges/valleys all parallel to **b**; the **bottom** is ridges/valleys all parallel to **a**. (Top and bottom corrugation directions differ — that mismatch is what forces the twist.)

**Step 2 — forced twist between layers.** To set a second layer on top, its bottom corrugations (∥**a**) must seat into the first layer's top corrugations (∥**b**). Because a≠b in direction, the upper layer must be **rotated by −φ about the z-axis** (`R` = rotation about Re₃) and lifted by c. Iterating,
```
T  =  ⋃_{m∈ℤ}  m·(0,0,c) + R^m L′ ,         L′ = L − c.
```
(More generally each layer may also be slid by any multiple of `R^m b` along its matching valleys; Danzer discretizes this. ([Baake–Frettlöh 2004, eq. 3](https://arxiv.org/abs/math-ph/0411052)).)

**Step 3 — no translation (⇒ non-periodic).** Since φ ∉ πℚ, **all layers have pairwise different orientations** `R^m Γ`. A translation `x` with `T + x = T` must map each layer to itself, so `x ∈ R^m Γ` for **every** m. Hence
```
x ∈ ⋂_{m∈ℤ} R^m Γ  =  {0}.
```
So **no nonzero translation** is a symmetry: the incommensurate SCD tiling is non-periodic (indeed *aperiodic* — see §5). (Caveat in the source: any *finite* stack can still share a coincidence-site sublattice of finite index; only the infinite intersection collapses to {0}.)

**Step 4 — the residual screw (⇒ only weakly aperiodic).** The map that rotates by −φ **and** lifts by c,
```
S : x ↦ R x + (0,0,c),
```
sends layer m to layer m+1 *and is a symmetry of the whole tiling*. The cyclic group `⟨S⟩ ≅ ℤ` is an **infinite group of Euclidean motions** with **no fixed compact fundamental domain** in the usual sense and containing no translation (since φ is irrational, no power `S^k` is ever a pure translation). The tiling therefore has a **screw axis** along Re₃. Goodman-Strauss's verdict, quoted by Socolar–Taylor: *"Goodman-Strauss calls the SCD tile **weakly aperiodic** because it admits a tiling with a cyclic group of symmetries involving finite (and nonzero) translations, in this case the screw operations along the twist axis."* ([arXiv:1009.1419](https://arxiv.org/abs/1009.1419)).

Socolar–Taylor add a second, *sharper* complaint that goes beyond "screw exists": **every single tile is the unit cell of a 2D-periodic layer**, and *"for the cases with a finite number of nearest-neighbor environments, any finite stack of layers is periodic in the two transverse directions."* So SCD's order is "visibly" two-dimensional-periodic-plus-twist — *"one can immediately grasp the global structure of simple 2D periodic lattices stacked with a twist"* — which is precisely **why the community said "this is not really what we are looking for."** ([arXiv:1009.1419](https://arxiv.org/abs/1009.1419)).

---

## 4. The contrast with 2D — what SCD changes

| | 2D (Euclidean plane) | 3D (Euclidean space) |
|---|---|---|
| Convex aperiodic monotile | **IMPOSSIBLE.** Every convex polygon that tiles edge-to-edge also tiles **periodically**; and the 15 convex-pentagon families (Rao 2017, computer-verified) exhaust convex monohedral tilers ([survey, arXiv:1508.01864](https://arxiv.org/pdf/1508.01864)). The hat/spectre are necessarily **non-convex** ([Kaplan 2025](https://arxiv.org/pdf/2509.12216): a fewer-than-13-gon einstein "would have to be non-convex"). | **POSSIBLE.** SCD is a **convex** polyhedron that tiles ℝ³ with no translation — *weakly* aperiodic. (PROVEN, 1988–94.) |
| Strongly aperiodic monotile | **PROVEN to exist** (hat 2023, spectre 2023; non-convex topological disks). | **OPEN.** No strongly aperiodic monotile (convex or not) known. |

**What SCD changes conceptually.** The 2D convexity obstruction is a *metric* fact: a convex tile is so rigid that any tiling can be "relaxed" to a periodic one. In 3D the **extra rotational degree of freedom about a stacking axis** is enough to defeat translational periodicity *even for a convex tile* — but that **same** extra degree of freedom is what supplies the screw symmetry. So 3D buys you weak aperiodicity from convexity *for free*, but the mechanism (a continuous/irrational twist about one axis) is intrinsically a **rank-deficient** one: it kills translations in all directions while leaving an infinite 1-parameter-flavored screw. Upgrading to **strong** aperiodicity means killing that last axis too — which is exactly the hard, open part.

---

## 5. Weakly vs strongly aperiodic — the precise definitions

There are three layers of "non-periodic," and they are genuinely different (all consistent with [Baake–Grimm 2012, arXiv:1210.0157](https://arxiv.org/abs/1210.0157); definitional convention due to **Goodman-Strauss**).

Let `per(Λ) = { t : t + Λ = Λ }` be the translation periods of a Delone set / tiling Λ, and let `X(Λ)` be its **hull** (the closure of its translation orbit in the local topology).

1. **Non-periodic:** `per(Λ) = {0}` (no nonzero translation period).
   - *Weaker still:* **non-crystallographic** = `per(Λ)` is not a full-rank lattice. For d ≥ 2, "non-crystallographic" is weaker than "non-periodic."
2. **(Topologically) aperiodic** — [Baake–Grimm Def. 1]: *"A locally finite point set Λ ⊂ ℝᵈ is called topologically aperiodic, or aperiodic for short, when **all elements of its hull X(Λ) are non-periodic**."* This discards "trivial" non-periodicity (their example: ℤ∖{0} is non-periodic, but its hull contains the periodic ℤ — so ℤ∖{0} is *not* aperiodic). One has
   `aperiodic ⇒ non-periodic ⇒ non-crystallographic.`
3. **Strongly aperiodic** — [Baake–Grimm Def. 2]: *"A locally finite point set Λ ⊂ ℝᵈ is called **strongly aperiodic** when it is aperiodic and when the **individual symmetry group of each element of X(Λ) is a finite group**."*

Equivalent operational forms in the tiling literature (Goodman-Strauss; [Einstein problem — Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem); [Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling)):
- **Strongly aperiodic protoset** = admits tilings, and **no** admitted tiling has an **infinite cyclic group of Euclidean motions** as symmetries (equivalently: no co-compact symmetry / no compact fundamental domain, *and* not even a 1-parameter screw/limit-translation).
- **Weakly aperiodic protoset** = admits tilings, none with a full translation lattice (no co-compact *translation* group), **but some admitted tiling may have an infinite cyclic symmetry** (e.g. a screw).

**Where SCD sits.** [Baake–Grimm Prop. 3]: a repetitive incommensurate SCD tiling **is aperiodic** (Def. 1 — every hull element is non-periodic). But the authors immediately note this is *"perhaps not entirely satisfactory, since an individual SCD tiling … may still possess a symmetry in the form of a screw axis … its symmetry group thus contains an infinite subgroup."* Hence **SCD is aperiodic but NOT strongly aperiodic** — the hull element has an **infinite** symmetry group `⟨S⟩`, violating Def. 2. By contrast Penrose and Ammann–Beenker have hull elements with only **finite** symmetry groups → those are strongly aperiodic in 2D.

**Two subtleties worth keeping (both load-bearing for us):**
- **Hull symmetry ≠ individual symmetry.** Strong aperiodicity (Def. 2) constrains the symmetry of *each individual tiling in the hull*, **not** the symmetry of the hull as a whole. [Baake–Grimm] stress *"it is possible to have strong aperiodicity in the presence of continuous symmetries of the hull"* — the **pinwheel tiling** is strongly aperiodic, yet its hull has full **circular (SO(2))** symmetry (the inflation introduces 2·arctan(½) ∉ πℚ, a new direction each step, so the fixed-point tiling has statistical circular symmetry). So "the hull rotates" is *allowed*; "an individual tiling carries an infinite isometry group" is what's *forbidden*. SCD fails on the second; pinwheel passes.
- **Socolar–Taylor's "partial translational symmetry"** ([arXiv:1009.1419, Def. 1](https://arxiv.org/abs/1009.1419)) is a third, finer lens: an operation `x ↦ Rx + e` (R a rotation, e≠0) leaving some *infinite subset* of tiles invariant. SCD is riddled with these (each layer is a 2D-lattice-invariant subset; the screw maps layer→layer). Their classification grades "degrees of nonperiodicity" by which partial symmetries survive — and rates SCD low precisely because so many do.

---

## 6. The precise open problem(s) — proven / open table (as of June 2026)

| # | Statement | Status | Date / source |
|---|---|---|---|
| P1 | A **convex** polyhedron (SCD) tiles ℝ³ with **no translational symmetry**. | **PROVEN** | Schmitt 1988; Conway & Danzer ~1990s ([Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem); [Baake–Frettlöh 2004](https://arxiv.org/abs/math-ph/0411052)) |
| P2 | SCD is **aperiodic** (all hull elements non-periodic) but **NOT strongly aperiodic** (hull element has infinite screw symmetry). | **PROVEN** | [Baake–Grimm 2012, Prop. 3 + Def. 2](https://arxiv.org/abs/1210.0157) |
| P3 | SCD tilings have **singular continuous** diffraction (pure-point only on the screw axis; no absolutely continuous part; rest on concentric cylinders) — **not** pure-point ⇒ **not a model set / not a regular cut-and-project set**. | **PROVEN** | [Baake–Frettlöh 2004](https://arxiv.org/abs/math-ph/0411052) |
| P4 | A **connected single 3D tile** enforcing aperiodicity **by shape alone** exists (the Socolar–Taylor 3D tile) — but it is only **weakly** aperiodic (admits a periodic/screw stacking). | **PROVEN** | [Socolar–Taylor 2011, Fig. 7](https://arxiv.org/abs/1009.1419) |
| P5 | **Strongly aperiodic protoSETS (≥2 tiles)** exist in ℝ³ (e.g. Danzer's ABCK 4 tetrahedra; many icosahedral substitution sets). | **PROVEN** | Danzer ABCK ([survey, arXiv:2003.13449](https://arxiv.org/pdf/2003.13449)) |
| **O1** | **Does a strongly aperiodic MONOTILE exist in Euclidean ℝ³?** (single tile, no infinite-cyclic-isometry tilings) | **OPEN** | confirmed open: [Kaplan 2025, arXiv:2509.12216](https://arxiv.org/pdf/2509.12216) |
| O1a | … if so, can it be **convex**? | **OPEN** (likely no, by analogy w/ 2D rigidity — but unproven in 3D) | — |
| O1b | … with **matching rules / decorations** allowed (not by shape alone)? | **OPEN** | — |
| O1c | … as a **connected topological ball** by **shape alone** (the true "3D einstein")? | **OPEN** | — |
| O2 | Can the **hat/spectre method** (metatiles + recognizable substitution, or the combinatorial-equivalence/incommensurability argument) be **lifted to 3D**? | **OPEN / speculative** — "could be adapted … daunting" | [Kaplan 2025](https://arxiv.org/pdf/2509.12216) |

**Important framing for our project:** O1 is the headline open problem and is *well-defined and high-value*. Note it is **not** the same as the Greenfeld–Tao result (see §7) — that is *translations-only* in *very high* dimension and is a different, complementary phenomenon.

---

## 7. Recent / adjacent work (dated, flagged)

**Verify-flag legend:** ✅ verified against primary source; ⚠️ secondary only / treat as a lead.

- ✅ **Greenfeld–Tao (2022–24), "aperiodic monotile by translation alone in high dimension."** They disproved the **periodic tiling conjecture**: in a *sufficiently high* (unknown exact) dimension `d`, a single finite tile tiles ℤᵈ (hence ℝᵈ) by **translations only** but **never periodically** (announcement [arXiv:2209.08451](https://arxiv.org/abs/2209.08451), full [arXiv:2211.15847](https://arxiv.org/abs/2211.15847), *Annals of Math.* 200(1):301–363, 2024; cited in [Kaplan 2025](https://arxiv.org/pdf/2509.12216)). The construction encodes a "Sudoku"-type functional equation as a single tiling equation in a group ℤ²×G₀ (finite abelian 2-group), all of whose solutions are non-periodic. *Different problem* from O1: translations-only (a *translational* aperiodic monotile), very-high-d, complicated/disconnected tile. It says "aperiodicity gets *easier* / more common as d grows" — a useful prior, but it does **not** give a 3D strongly-aperiodic monotile, and there are no rotations/screws in play.
- ✅ **Kaplan, "The Path to Aperiodic Monotiles" (Sept 2025, arXiv:2509.12216).** The most recent authoritative survey-with-opinion. Explicitly states O1 is open, that hat-style ideas/algorithms "could be adapted to work in 3D" but deducing candidate behaviour is "daunting," and frames SCD as existence-proof-plus-cautionary-tale. **Best single recent citation for the open status.**
- ✅ **Maiti, "Unboundedness of the Heesch Number for Hyperbolic Convex Monotiles" (March 2026, arXiv:2603.27827).** *(This is the citation our planar `README.md` flagged "verify" — now verified.)* It constructs, in the **hyperbolic plane**, an infinite family of **convex aperiodic monotiles** (duals of homogeneous tilings) with rational inner angles. **Crucial correction:** these are described as **weakly aperiodic convex monotiles**, *not* strongly aperiodic. So the hyperbolic-convex case currently parallels SCD (convex + weak), and a **strongly** aperiodic convex monotile remains open in the hyperbolic plane too. (2D-hyperbolic, not 3D — relevant only as method analogy.)
- ✅ **Walton, "Recognisability for generalised hierarchical pattern spaces of FLC" (Sept 2025, rev. May 2026, arXiv:2509.21001).** Proves **recognizability / unique substitution pre-images** for general FLC patterns with *no minimality requirement* (answering a Cortez–Solomyak question). Directly relevant proof-technique infrastructure for §8 — it is the kind of theorem one would invoke to certify a 3D substitution tile's aperiodicity via our non-factorization route, in a setting general enough to cover odd point sets.
- ⚠️ **"Observation of an aperiodic polariton monotile" (May 2026, arXiv:2605.13206).** Physics/experiment. **NOT a 3D einstein** — it optically sculpts the **2D** hat/spectre monotile in a microcavity (Bragg peaks, Dirac-like features). Listed only to **rule it out** as a 3D result; it is a planar realization.
- **No verified claim of a strongly aperiodic 3D monotile (or a "3D hat/spectre") exists as of June 2026.** Multiple targeted searches (2023–2026, arXiv + secondary) returned only SCD, Socolar–Taylor 3D (weak), Danzer ABCK (multi-tile), and the high-d Greenfeld–Tao translation-only result. **If a future search surfaces a "3D einstein" preprint, treat as unverified until the aperiodicity proof and the strong-vs-weak claim are checked against §5 Def. 2.**

**3D *protoset* landscape (context, all PROVEN, all >1 tile):** Danzer's **ABCK** (4 tetrahedra, icosahedral, simple geometric/packing local rules, inflation-stable); Ammann's 3D rhombohedra; many icosahedral substitution tilings from the D₆ lattice ([arXiv:2003.13449](https://arxiv.org/pdf/2003.13449)). These are genuinely strongly aperiodic and *are* model sets (pure-point diffraction) — but they are **not monotiles**. The monotile gap (O1) is the whole game.

---

## 8. How aperiodicity is PROVEN for a 3D tile (techniques)

Five techniques, in roughly increasing alignment with our shadow/strict-extension lens. (Cross-ref planar pillars 03, 05, 06.)

1. **Direct symmetry-group computation (the SCD method).** Show every legal tiling is forced into a known parametric form, then compute `per(·)` directly. SCD: forced layers ⇒ translations lie in `⋂_m R^m Γ = {0}`. *Pro:* elementary, exact. *Con:* only yields the symmetry actually present — it transparently exposes the residual screw, i.e. it **proves weak, not strong**, aperiodicity. Used in [Baake–Frettlöh 2004](https://arxiv.org/abs/math-ph/0411052).

2. **Incommensurability / number-theoretic obstruction (the spectre-style metric argument, 3D analog).** Embed the candidate in a *continuum of combinatorially equivalent* tiles; show two degenerate members tile periodically with **incommensurable** lattice constants (e.g. lengths mixing √3 and 1); a periodic tiling of a generic member would force an algebraic relation between those lattices that cannot hold (à la "√2 irrational"). This is **Proof B** of the hat ([survey arXiv:2310.06759](https://arxiv.org/html/2310.06759v2)); in 3D one would need a 3-parameter combinatorial family and a volume/length incommensurability. *Status:* no 3D instance executed; this is the most plausible route to **strong** aperiodicity if a candidate family is found.

3. **Hierarchical substitution + recognizability (the hat Proof A, and our T2).** Prove tiles group **uniquely** into metatiles obeying a primitive **inflation** rule; **recognizability** (= unique composition, Mossé/Solomyak; generalized FLC version [Walton 2025, arXiv:2509.21001](https://arxiv.org/abs/2509.21001)) then forces a unique supertile hierarchy at every scale. A symmetry must preserve that hierarchy at all scales; supertiles grow without bound ⇒ no fixed isometry can preserve them ⇒ **strongly** aperiodic (this argument kills *all* infinite isometries, not just translations, when the inflation injects new directions — cf. pinwheel). **This is the technique most likely to deliver O1**, and the one our framework is built around. In 3D the inflation factor must be **Perron** (necessary) and, for pure-point order, **Pisot/Salem** (e.g. a cubic Pisot unit; τ³ is a natural candidate eigenvalue).

4. **Local-rules ↔ projection (cut-and-project certification, our T-shadow).** Realize the tiling as a **cut/section of a higher-dim periodic lattice** (superspace), then certify aperiodicity as **strict extension / non-factorization** (the section does not descend to a periodic quotient). For 3D quasicrystals this is **superspace crystallography** (6D→3D for icosahedral; planar pillar 04). Le's algebraicity obstruction and Bédaride–Fernique's decidable coincidence criterion (pillar 06) govern which slopes admit finite local rules. **Caveat from §P3:** SCD itself is **not** a model set (singular continuous diffraction), so this certificate route *does not apply to SCD as-is* — which is precisely the diagnostic that SCD is "the wrong kind" of aperiodic. A strongly-aperiodic 3D monotile we would *want* to be a (Pisot) model set so this certificate **does** apply.

5. **Hull-as-inverse-limit + topological invariants (Anderson–Putnam, gap-labeling; our T1/T2).** Build the **branched manifold** (AP complex) for the 3D substitution; the hull is its **inverse limit** under the inflation self-map. Aperiodicity ⇔ the bonding maps are non-degenerate (border-forcing ⇒ recognizability); Čech cohomology / **Bellissard gap-labeling** then provides finite topological invariants (patch-frequency module, the Perron eigenvalue audit). Works verbatim in 3D ([planar pillar 05]; Anderson–Putnam 1998; Sadun–Williams 2003).

**Why O1 is hard, in technique terms:** Techniques 1–2 prove *non-periodicity* readily but a convex/simple tile tends to leave a screw (technique 1's transparency is also its limitation). Forcing a *recognizable hierarchy* (technique 3) **by the geometry of a single 3D shape** — with no matching rules and ideally convex — is the crux: you must encode all the long-range hierarchical information **on the 2D boundary of one polyhedron**, exactly the "spooky action at a distance" Kaplan names, and then *also* defeat every screw. Nobody has exhibited a single 3D shape that does this.

---

## 9. Authoritative sources (titles + URLs)

**Primary (construction & proofs):**
- M. Baake, D. Frettlöh, *SCD Patterns Have Singular Diffraction*, J. Math. Phys. 46 (2005). [arXiv:math-ph/0411052](https://arxiv.org/abs/math-ph/0411052) — **exact SCD construction (§1) + diffraction (singular continuous).**
- M. Baake, U. Grimm, *On the notions of symmetry and aperiodicity for Delone sets*, Symmetry 4 (2012). [arXiv:1210.0157](https://arxiv.org/abs/1210.0157) — **the formal Def. 1–3 (aperiodic / strongly aperiodic / statistically aperiodic); SCD = aperiodic-not-strongly; pinwheel subtlety.**
- J. Socolar, J. Taylor, *Forcing Nonperiodicity With a Single Tile*, Math. Intelligencer 34 (2012). [arXiv:1009.1419](https://arxiv.org/abs/1009.1419) — **"weakly aperiodic" verdict on SCD; partial-translational-symmetry definition; the connected 3D Socolar–Taylor tile (Fig. 7).**
- D. Smith, J. S. Myers, C. Kaplan, C. Goodman-Strauss, *An aperiodic monotile*, Combinatorial Theory 4 (2024). [arXiv:2303.10798](https://arxiv.org/abs/2303.10798); chiral: [arXiv:2305.17743](https://arxiv.org/abs/2305.17743) — **the 2D einstein; proof techniques A (recognizable substitution) & B (incommensurability).**

**Surveys / status:**
- C. Kaplan, *The Path to Aperiodic Monotiles* (2025). [arXiv:2509.12216](https://arxiv.org/pdf/2509.12216) — **best recent statement of the 3D open problem + Greenfeld–Tao high-d.**
- *Planar aperiodic tile sets: from Wang tiles to the Hat and Spectre monotiles* (2023). [arXiv:2310.06759](https://arxiv.org/html/2310.06759v2).
- [Einstein problem — Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem); [Aperiodic tiling — Wikipedia](https://en.wikipedia.org/wiki/Aperiodic_tiling) — Goodman-Strauss weak/strong convention.
- [Conway on his aperiodic biprism — Geometry Junkyard (Eppstein)](https://ics.uci.edu/~eppstein/junkyard/biprism.html); [SCD biprism — Polytope Wiki](https://polytope.miraheze.org/wiki/Schmitt%E2%80%93Conway%E2%80%93Danzer_biprism); [Gyrobifastigium/SCD prototile — Wikipedia](https://en.wikipedia.org/wiki/Gyrobifastigium).

**Adjacent / recent (dated, see §7):**
- A. Maiti, *Unboundedness of the Heesch Number for Hyperbolic Convex Monotiles* (Mar 2026). [arXiv:2603.27827](https://arxiv.org/abs/2603.27827) — hyperbolic **weakly** aperiodic convex monotiles (corrects our README's "verify" flag).
- J. Walton, *Recognisability for generalised hierarchical pattern spaces of FLC* (2025/26). [arXiv:2509.21001](https://arxiv.org/abs/2509.21001) — general recognizability infrastructure.
- 3D protosets: Danzer ABCK / D₆ icosahedral — [arXiv:2003.13449](https://arxiv.org/pdf/2003.13449).
- *(ruled out as 3D)* [arXiv:2605.13206](https://arxiv.org/abs/2605.13206) — 2D polariton realization of the hat.

---

## 10. Relevance to our shadow / strict-extension approach

**Headline: the SCD screw symmetry is exactly a non-factorization / holonomy phenomenon — but of the *wrong, abelian* kind, and that is the diagnostic that tells our framework what to aim for.**

**(a) SCD *is* a shadow — of a degenerate, almost-periodic upstairs.** Read SCD through the cut-and-project lens: the forced 2D layer is a genuine periodic lattice `Γ ⊂ ℝ²`, and the stack is `⋃_m S^m L` for the screw `S = R⊕(lift c)`. The "higher structure" is essentially **ℝ² (periodic) ⋊ ℤ (irrational rotation)** — a *crossed product / mapping torus of an irrational rotation of the plane lattice's orientation*. The obstruction to descending to a period is `⋂_m R^m Γ = {0}` — an **emptiness-of-the-intersection**, i.e. the orbit of the lattice under the irrational rotation never re-aligns. In our language this is a **strict extension that fails to factor through a translation quotient**: π₁ (the stacked object, indexed by the screw) does not factor through π₀ (any single periodic layer). So SCD *does* fit "audited shadow of a higher periodic layer" — the layer is periodic, the gluing is the non-descending datum.

**(b) But the non-factorization here is *holonomy around a 1-parameter abelian screw*, not a recognizable hierarchical lift.** The "holonomy" is literally the rotation angle φ accumulated per layer (the monodromy of the mapping torus). Because φ ∈ ℝ/πℚ is a *single real number* generating a *ℤ* action, the residual symmetry group is `⟨S⟩ ≅ ℤ` — **infinite cyclic, abelian, one-dimensional**. That is exactly what Def. 2 (strong aperiodicity) forbids. Contrast our target: a **recognizable Pisot inflation** (technique §8.3) whose holonomy is the *substitution itself*, injecting **new directions at every scale** (pinwheel-style) so that **no** infinite isometry — translation *or* screw — survives. The SCD screw is a **rank-1, fixed-axis** holonomy; a strong-aperiodic monotile needs **rank-0 residual isometry** (only finite groups in the hull), achieved by **scale-mixing** rather than a single fixed-axis twist.

**(c) The diffraction signature is the cleanest certificate-level diagnostic (P3).** SCD's diffraction is **singular continuous off the screw axis** ([Baake–Frettlöh](https://arxiv.org/abs/math-ph/0411052)) — i.e. it is **not a regular model set / not a clean cut-and-project shadow** in the pure-point sense pillar 02 demands. **Pure-pointness is our "legal descent" certificate.** So SCD *fails our descent-legality audit*: its upstairs is the wrong object (a real-rotation crossed product, whose internal space is a **circle/cylinder**, not a Euclidean window — note Baake–Frettlöh find the spectrum supported on **concentric cylinders**, the dual of that circular internal space). A solution to O1 through our lens should be engineered to have **pure-point diffraction** ⇒ a genuine **Euclidean-window cut-and-project / Pisot model set** ⇒ automatically no continuous screw freedom.

**(d) What a solution would look like in our terms.** A strongly aperiodic 3D monotile, through the shadow/strict-extension framework, would be:
   1. **Upstairs:** a periodic lattice `L` in superspace ℝ^{3+k} (e.g. 6D→3D, icosahedral) with an **irrational but finite, scale-injecting** slope — *not* a crossed product by a circle action.
   2. **Inflation:** a primitive substitution with a **cubic Pisot (ideally unit) eigenvalue** — `τ³ = 2τ+1 ≈ 4.236` is the natural lead, being the volume-scaling of an icosahedral/Penrose-type 3D inflation; the **Perron** condition is necessary, **Pisot** gives pure-point order (pillars 03, 04).
   3. **Certificate:** **recognizability** of that 3D substitution (Mossé/Solomyak; general FLC form [Walton 2025](https://arxiv.org/abs/2509.21001)) = our **non-factorization** δ_fact ≠ ∅; this is what upgrades weak→strong by killing the screw.
   4. **Hull:** the **Anderson–Putnam inverse limit** of the 3D branched manifold under inflation (pillar 05) = our T2; **gap-labeling** (Bellissard) supplies the eigenvalue audit = our T1.
   5. **Monotile collapse:** the single-tile reduction is, by analogy with the hat, a **fractal-window reprojection** (a 3D Rauzy/internal window whose shape collapses the protoset to one prototile) — the genuinely hard, open design step.

**(e) Sharp statement of the gap we'd be closing.** SCD demonstrates **convex ⇒ weak in 3D for free** via an abelian fixed-axis screw (rank-1 residual holonomy, singular-continuous spectrum, circular internal space). Our framework's job is to **trade that abelian screw for a Pisot-recognizable hierarchy** (scale-mixing holonomy, pure-point spectrum, Euclidean internal window) carried by a **single** 3D shape — which is exactly O1c. The screw being "abelian, rank-1, fixed-axis" is precisely *why* SCD is only weak; our non-factorization certificate is well-suited to detect and forbid it (it shows up as a residual ℤ-period in the hull, i.e. δ_fact failing to be a finite-symmetry quotient). **So yes — the SCD screw is a non-factorization/holonomy phenomenon, and naming it as the *abelian, rank-deficient* case sharpens what "strong" must add: a recognizable, scale-mixing, Pisot lift.**

---

*Document status: 3D focused deep-dive, June 2026. Existence of a strongly aperiodic 3D monotile (O1) is OPEN as of this date (confirmed [Kaplan 2025](https://arxiv.org/pdf/2509.12216)). All "recent" claims dated and verify-flagged in §7.*
