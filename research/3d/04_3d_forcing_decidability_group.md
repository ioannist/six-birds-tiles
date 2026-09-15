# 04 — Forcing aperiodicity in 3D: matching rules, decidability, and the group-theoretic / Greenfeld–Tao angle

*Focused 3D deep-dive for the "shadow / strict-extension" program. The local matching-rule layer
is our **π₀** (an SFT / tiling of finite type); the central question is whether **local rules can
FORCE the higher hierarchical layer in 3D**, and how *rare* a local rule with a consistent lift is.
This document is the 3D counterpart to the 2D pillar
[../06_matching_rules_SFT_decidability.md](../06_matching_rules_SFT_decidability.md): it ports the
forcing/decidability/group-theoretic machinery to ℤ³ and 𝔼³, states the Greenfeld–Tao high-dimensional
results precisely, and assembles the **3D rarity argument**.*

---

## 0. Overview — the four-way landscape in 3D

There are **four distinct "forcing in 3D" questions**, and they sit at very different stages. Keeping
them apart is the single most important thing in this dossier, because the literature routinely
conflates them and the conflation would mislead our design.

| Question | What forces what | 3D status (date) |
|---|---|---|
| **(A) Tile SETS force aperiodicity** | a finite set of *decorated/matching* prototiles admits tilings, all non-periodic | **PROVEN, easy in 3D.** Domino problem undecidable on ℤ^d for all d ≥ 2 ⇒ strongly aperiodic SFTs exist in every dimension ≥ 2 (Berger 1966; Robinson 1971; Culik–Kari; Mozes). |
| **(B) Matching rules force a specific 3D quasicrystal (icosahedral)** | a finite set of face-decorated zonohedra forces the cut-and-project icosahedral order (our π₀ → projection bridge in 3D) | **PROVEN for WEAK rules** (Katz 1988; Socolar 1990; Levitov 1988). The icosahedral 3-plane in ℝ⁶ is *algebraic/quadratic*, hence inside Le's enforceable locus. |
| **(C) A single geometric tile forces aperiodicity in 𝔼³ (the 3D "einstein")** | one connected shape, isometries allowed, tiles only non-periodically | **WEAK version PROVEN** (Schmitt 1988 → Schmitt–Conway–Danzer; Socolar–Taylor 3D). **STRONG version OPEN** — no strongly-aperiodic 3D monotile is known (all known ones admit a screw axis / periodic layer-shift). |
| **(D) A single tile forces aperiodicity for *translations* in ℤ^d (Greenfeld–Tao)** | one finite cluster, **translations only**, tiles ℤ^d (or a virtually-ℤ² group) only non-periodically | **PROVEN in "sufficiently large" fixed dimension** (Greenfeld–Tao 2022/2024); **connected** version PROVEN (Greenfeld–Kolountzakis); **OPEN whether any such tile exists in d = 3** (Greenfeld conjectures *no* in 3D, plausible in 4D). Monotiling **undecidable with dimension as input** (2023); **OPEN at every fixed d > 2**. |

The take-away for the program, up front:

- **(A) and (B) are the good news.** Forcing a 3D *quasicrystalline higher layer* with **a finite set
  of matching tiles** is a solved, classical fact — the icosahedral case is exactly as enforceable as
  Penrose, because its slope is algebraic/quadratic (Le's locus). Our π₀ → π₁ forcing question has a
  positive 3D answer **for tile sets**.
- **(C) is the prize and the warning.** Collapsing the tile *set* to a single *geometric* tile that is
  **strongly** aperiodic in 𝔼³ is *open*: the only known 3D monotiles "leak" a screw axis. The hat/spectre
  collapse (matching rule dissolved into shape) has **no known 3D analogue**.
- **(D) is a different problem wearing the same clothes.** Greenfeld–Tao force aperiodicity with a single
  tile **under translations only, in very high dimension, with a disconnected-by-default cluster**. It is
  *not* a geometric strongly-aperiodic 3D monotile and gives *no* construction at d = 3 — but its
  **method** (Sudoku / functional equations / undecidability) is the sharpest modern statement of "almost
  no local rule lifts," and is a candidate route *and* a candidate impossibility-flag for us.

---

## 1. (A) Tile **sets** in 3D: the domino problem and strongly-aperiodic SFTs

### 1.1 The domino problem is undecidable on ℤ^d for every d ≥ 2

The domino problem — *does a finite set of decorated unit cubes / Wang cubes admit an edge-to-edge
tiling of all of ℤ^d?* — is **undecidable for ℤ², and therefore for every ℤ^d, d ≥ 2**: a ℤ^d instance
can simulate a ℤ² instance by making the extra d − 2 directions trivial (constant layers), so 2D
undecidability immediately transfers upward. (Berger 1966; surveyed in
[Jeandel–Vanier, *The Undecidability of the Domino Problem*](https://link.springer.com/chapter/10.1007/978-3-030-57666-0_6),
[PDF](https://www.lacl.fr/pvanier/rech/cirm.pdf).)

> **Status: PROVEN (Berger 1966; transfers to all d ≥ 2).** The hard direction is ℤ²; higher dimensions
> are *no harder* for this question.

### 1.2 Undecidability forces strongly-aperiodic tile SETS in 3D

The classical implication "undecidability ⇒ an aperiodic tile set exists" (because if every tiling set
admitted a periodic tiling the problem would be co-semi-decidable; see
[../06_matching_rules_SFT_decidability.md §1.2](../06_matching_rules_SFT_decidability.md)) holds verbatim
in ℤ^d. Concretely:

- **Berger/Robinson lift directly.** A Robinson tile set laid in two coordinates with inert extra layers
  is a **strongly aperiodic SFT in ℤ^d** for every d ≥ 2. ("Strongly aperiodic" for a *subshift/tile set*
  = every configuration has trivial stabilizer, i.e. no nonzero period.)
- **Mozes (1997)** constructed **strongly aperiodic tile sets on symmetric spaces** (semisimple Lie
  groups) — a much stronger geometric statement than ℤ^d, confirming the 3D Euclidean case a fortiori.
  ([Wikipedia, Einstein problem](https://en.wikipedia.org/wiki/Einstein_problem); Mozes, *J. Anal. Math.* 1997.)

> **Status: PROVEN.** Strongly-aperiodic *tile sets* (many prototiles, with matching decorations) are
> abundant in 3D. There is **no obstruction** to forcing strong aperiodicity in 𝔼³ *if you are allowed
> several decorated prototiles*. The entire 3D difficulty (question C) is the **collapse to one tile**.

This is the cleanest single fact for our program: **the SFT layer (π₀) can be strongly aperiodic in 3D.**
What we cannot yet do is make that SFT the *shape-adjacency* SFT of a single solid.

---

## 2. (B) Matching rules forcing 3D **icosahedral** quasicrystals — the π₀ → projection bridge in 3D

This is the direct 3D analogue of the Penrose / Ammann–Beenker local-rules story. The cut-and-project
"upstairs" for the icosahedral quasicrystal is a **3-plane E ⊂ ℝ⁶** with the icosahedral group acting;
the two **Ammann rhombohedra** (acute + obtuse golden rhombohedra) are the canonical-projection
prototiles. The question is whether **face decorations (matching rules) force E** — i.e. compel a local
observer into the icosahedral projection.

### 2.1 Katz (1988): theory of matching rules for the 3D Penrose (icosahedral) tiling ★

**A. Katz, "Theory of matching rules for the 3-dimensional Penrose tilings," *Commun. Math. Phys.* 118
(1988) 263–288.** Katz studies packings of the **two Ammann rhombohedra** and equips their faces with
**matching decorations** so that any legal tiling is a quasiperiodic 3D Penrose (icosahedral) tiling.
This is the foundational proof that the 3D icosahedral order **is enforceable by finite face-matching
rules**. ([Springer record](https://link.springer.com/article/10.1007/bf01218580); restated in
[Bédaride–Fernique and the *Robust minimal matching rules* literature](https://arxiv.org/abs/1809.10614).)

The decorations are most transparently encoded via **Ammann planes** — the 3D analogue of Ammann bars:
a quasilattice of planes whose forced continuity across faces *is* the matching rule. (See the
icosahedral-substitution and Ammann-plane treatments
[Madison, "Substitution rules for icosahedral quasicrystals," *RSC Adv.* 2015](https://pubs.rsc.org/en/content/articlehtml/2015/ra/c4ra09524c).)

### 2.2 Levitov (1988) and Socolar (1990): WEAK matching rules suffice for icosahedral

- **Levitov (1988)** introduced **strong vs weak** local rules and gave **necessary arithmetic
  conditions**; weak local rules exist for almost all quadratic 2D quasicrystals **and for the icosahedral
  case**. ([Levitov, *CMP* 119:627 (1988)](https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-119/issue-4/Local-rules-for-quasicrystals/cmp/1104162600.pdf))
- **Socolar (1990), "Weak matching rules for quasicrystals," *CMP* 129:599** defines **weak matching
  rules** as local rules forcing **perp-space ("phason") fluctuations to be uniformly bounded** (the lift
  stays within a bounded slab of E, rather than the unit-thickness slab that *strong* rules demand), and
  shows the construction yields **weak matching rules for octagonal, decagonal, dodecagonal AND
  icosahedral symmetry**. ([Springer record](https://link.springer.com/article/10.1007/BF02097107).)

> **Strong vs weak (recap, applied to 3D).** *Strong* rules ⇒ true digitization (unit-thickness lift);
> *weak* rules ⇒ bounded-thickness lift. For the **icosahedral** quasicrystal, **weak** matching rules are
> established; the existence of **strong** (unit-thickness) icosahedral matching rules is the subtler
> question Levitov/Katz address via Ammann-plane decorations.

### 2.3 Why this works: the icosahedral slope is *algebraic/quadratic* — inside Le's locus

The decisive structural reason the 3D icosahedral case is forceable is the **same** as in 2D Penrose: the
3-plane E ⊂ ℝ⁶ is built over **ℚ(√5)** (golden ratio), so it is **algebraic** and in fact **quadratic** —
exactly the locus that **Le's obstruction** (1997) permits.

> **Le's theorem (1997)** — *a (generic) slope admitting weak local rules is necessarily **algebraic**
> (its generating vectors lie in a common algebraic number field).*
> ([T.T.Q. Le, "Local rules for quasiperiodic tilings," NATO ASI C-489, Kluwer 1997, pp. 331–366];
> restated as Corollary 1 in [Bédaride–Fernique, arXiv:1812.06863](https://arxiv.org/pdf/1812.06863).)

Le's result is **dimension-general** (it concerns slopes in any Grassmannian G(n, d)), so it is exactly
the **3D projection-side rarity statement** we need (see §5). The sufficiency side in higher dimension —
**Le–Piunikhin–Sadov (1992)** "every quadratic plane of ℝ^k admits colored weak local rules" and
**Le–Piunikhin (1995)** "quadratic d-planes of ℝ^{2d}" — covers the icosahedral 3-plane.
([Le–Piunikhin–Sadov, *CMP* 1992](https://link.springer.com/article/10.1007/BF01218348);
[Le–Piunikhin, *CMP* 1995](https://link.springer.com/article/10.1007/BF02096563).)

### 2.4 The gap from (B) to (C): tile set ⇏ single tile

Katz/Socolar give a **finite set of decorated prototiles** (two rhombohedra + face markings). This is
**not** a single geometric monotile:

1. There are **two** prototiles, not one.
2. The forcing lives in the **decorations** (Ammann-plane continuity), not in the bare shapes — the
   undecorated rhombohedra tile periodically.
3. The aperiodicity is the **weak / quasicrystalline** kind (bounded perp-space), and the *tiling space*
   is strongly aperiodic only in the SFT sense, not the single-solid sense.

> **The 3D analogue of the hat would be: dissolve the Katz/Ammann decorations into the *shape* of a
> single solid, with isometries.** No such collapse is known. This is precisely question (C).

---

## 3. (C) The single **geometric** 3D tile (the 3D einstein): weak is solved, strong is OPEN

### 3.1 Definitions: weakly vs strongly aperiodic (Goodman-Strauss), in 3D

After the SCD tile forced a re-examination of "non-periodic," **Goodman-Strauss** proposed the now-standard
distinction ([Wikipedia, Einstein problem](https://en.wikipedia.org/wiki/Einstein_problem);
[The Aperiodical, "Now that's what I call an aperiodic monotile!"](https://aperiodical.com/2023/05/now-thats-what-i-call-an-aperiodic-monotile/)):

> A tiling / tile is **strongly aperiodic** if it admits **no infinite cyclic group of Euclidean motions**
> as symmetries; a tile set is called *strongly aperiodic* only if it **enforces** this. Otherwise it is
> **weakly aperiodic** (it may admit an infinite cyclic symmetry group — e.g. a **screw motion** =
> rotation composed with translation along the axis — while admitting *no pure translation*).

The crucial 3D subtlety: **"no translation" is much weaker than "no infinite cyclic symmetry"**, because
3D opens up **screw axes**. A monotile can rule out translations yet still tile in helical columns.

### 3.2 The Schmitt–Conway–Danzer (SCD) tile — a *convex* 3D monotile, only WEAKLY aperiodic

- **Peter Schmitt (1988)** found a single aperiodic prototile in 𝔼³; **Conway** and **Danzer** made it
  **convex** — the **Schmitt–Conway–Danzer (SCD) biprism** (a convex polyhedron with 8 faces).
  ([Einstein problem, Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem);
  [Polytope Wiki](https://polytope.miraheze.org/wiki/Schmitt%E2%80%93Conway%E2%80%93Danzer_biprism).)
- It tiles 𝔼³ in **planar layers** that are **rotated by a fixed irrational multiple of π** from layer to
  layer. Hence **no tiling has a translation symmetry**, but tilings **do** have a **screw symmetry**
  (rotation through an irrational angle + translation along the axis), which generates an infinite cyclic
  symmetry group.
- Therefore the SCD tile is **WEAKLY aperiodic**, *not* strongly aperiodic. The screw axis is, in
  Goodman-Strauss's phrase, "uncomfortably close to translation."

> **Status: PROVEN weakly aperiodic (Schmitt 1988 / Conway–Danzer); NOT strongly aperiodic.** It is
> simultaneously an **existence proof** (a convex 3D monotile that never tiles periodically) **and a
> cautionary tale** about what "aperiodic" should mean in 3D. ([Kaplan/Isohedral overview](https://isohedral.ca/aperiodic-monotiles/).)

### 3.3 The Socolar–Taylor 3D monotile — a *connected* einstein from dissolved matching rules, still WEAK

The 2D Socolar–Taylor tile is a **marked hexagon** whose local matching rule (a next-nearest-neighbour
orientation constraint) forces non-periodic, Sierpiński-triangle-structured tilings — but the rule is
**known to be realizable only by a disconnected shape in 2D**. Socolar–Taylor's key 3D remark
([Socolar–Taylor, "Forcing nonperiodicity with a single tile," *Math. Intelligencer* 34 (2012) 18–28,
arXiv:1009.1419](https://arxiv.org/pdf/1009.1419);
[Socolar–Taylor tile, Wikipedia](https://en.wikipedia.org/wiki/Socolar%E2%80%93Taylor_tile)):

- The 2D matching rule **can be implemented geometrically by a single CONNECTED solid in 3D** — a genuine
  3D monotile whose *shape alone* enforces the rule (the markings become 3D protrusions/recesses).
- But that 3D tile **admits a period**: it tiles in **non-periodic 2D layers** that are **translated
  (shifted) from one layer to the next**, so the stack has a translation symmetry perpendicular to the
  layers. Hence it is again only **WEAKLY aperiodic**.
- Assembling physical copies **requires reflections** (orientation-reversing), i.e. effectively access to
  a 4th dimension.

> **Status: PROVEN — a connected 3D monotile whose shape forces non-periodicity exists (Socolar–Taylor),
> but it is WEAKLY aperiodic (periodic layer-shift) and needs reflections.** This is the closest thing to
> a 3D hat, and it falls short *exactly* on strong aperiodicity.

### 3.4 The bottom line on (C): the open problem, precisely

> **OPEN (as of 2026):** *Is there a single geometric prototile in 𝔼³ that tiles space but admits
> **no** tiling with an infinite cyclic symmetry group (no translation **and** no screw) — i.e. a
> **strongly-aperiodic 3D monotile**?* Every known 3D monotile (SCD, Socolar–Taylor, and variants) tiles
> screw-symmetrically or with a periodic layer-shift. There is also **no analogue of the hat's
> shape-only, no-decoration collapse** in 3D.
> ([Kaplan, *The Path to Aperiodic Monotiles*, arXiv:2509.12216](https://arxiv.org/pdf/2509.12216);
> [Isohedral overview](https://isohedral.ca/aperiodic-monotiles/); [Aperiodical](https://aperiodical.com/2023/05/now-thats-what-i-call-an-aperiodic-monotile/).)

Kaplan's expectation (informal): "it seems quite reasonable to assume that something like the hat exists
in 3D, but as in 2D it's hard to find (and probably harder to reason about, even once you've found it)."

---

## 4. (D) Greenfeld–Tao: the high-dimensional translational monotile, decidability, and what it does/doesn't say

This is the deepest recent forcing/decidability result, and the one most often misread as "a 3D aperiodic
monotile." It is a **different object** — translations only, very high dimension, disconnected by default —
but its *machinery* is exactly the modern form of "almost no local rule admits a consistent lift."

### 4.1 The Periodic Tiling Conjecture (PTC)

> **PTC (discrete).** *If a finite set F ⊂ ℤ^d tiles ℤ^d by translations (some A ⊆ ℤ^d with A ⊕ F = ℤ^d),
> then F also tiles ℤ^d **periodically**.* (Continuous version: bounded measurable Ω ⊂ ℝ^d.)
> ([Tao's blog, "A counterexample to the periodic tiling conjecture"](https://terrytao.wordpress.com/2022/09/19/a-counterexample-to-the-periodic-tiling-conjecture/).)

PTC was **proven in d = 1** (trivial) and **d = 2** (Bhattacharya 2009/2020, for a single tile). It was
widely believed to hold in all dimensions — which would have *forbidden* a translational aperiodic
monotile and forced decidability of monotiling.

### 4.2 Greenfeld–Tao (2022/2024): PTC is FALSE in sufficiently high dimension ★

**R. Greenfeld & T. Tao, "A counterexample to the periodic tiling conjecture," announcement
[arXiv:2209.08451](https://arxiv.org/abs/2209.08451), full
[arXiv:2211.15847](https://arxiv.org/abs/2211.15847), *Annals of Math.* 200(1) (2024) 301–363
([journal](https://annals.math.princeton.edu/2024/200-1/p05)).**

> **Theorem (Greenfeld–Tao).** Both the discrete and continuous periodic tiling conjectures **fail for
> sufficiently large d**. Concretely they build a counterexample in a group **G = ℤ² × G₀**, where **G₀ is
> a finite abelian 2-group**: a **single tile** F ⊆ G that tiles G by translations, but **all** of its
> tilings are **non-periodic**. Embedding G into ℤ^d / ℝ^d gives the Euclidean counterexamples.

Precise features (these matter for not over-claiming):

- **Single tile.** It is a genuine **monotile** (after their 2021 two-tile precursor). ✔
- **Translations only.** No rotations/reflections are used or allowed. ✔
- **Group is "virtually ℤ²".** The honest dimension count is **2 + (size of G₀)**: it is ℤ² *decorated by a
  finite group*, then unfolded into ℤ^d. The construction is "as low-dimensional as their method reaches,"
  which is *why* the resulting d is huge, not small.
- **Disconnected by default.** The tile is a **finite union of unit cubes that need not be connected**.
  ([Tao's blog](https://terrytao.wordpress.com/2022/09/19/a-counterexample-to-the-periodic-tiling-conjecture/);
  [Quanta, "'Nasty' Geometry Breaks Decades-Old Tiling Conjecture"](https://www.quantamagazine.org/nasty-geometry-breaks-decades-old-tiling-conjecture-20221215/).)
- **Dimension is astronomically large and unoptimized.** They made no attempt to optimize; a literal
  execution gives bounds like ~2^(100^100). Tao: *"it's very, very far from being optimal."*
  ([Quanta](https://www.quantamagazine.org/nasty-geometry-breaks-decades-old-tiling-conjecture-20221215/).)

**Construction idea (the "Sudoku" method).** Encode a system of **functional equations** as a single
**tiling equation** A ⊕ F = ℤ² × G₀. The relevant solutions are graphs of functions that are **p-adically
structured** (e.g. f_p(n) = last nonzero base-p digit of n) — *almost periodic but never periodic*. A
"giant Sudoku puzzle" (rows/diagonals constrained to such sequences) is shown to have **solutions that
exist but are all non-periodic**, via shear/"Tetris" elimination of constant rows.
([Tao's blog](https://terrytao.wordpress.com/2022/09/19/a-counterexample-to-the-periodic-tiling-conjecture/);
[Quanta](https://www.quantamagazine.org/nasty-geometry-breaks-decades-old-tiling-conjecture-20221215/).)

### 4.3 Greenfeld–Kolountzakis: the counterexample can be made CONNECTED ★

**R. Greenfeld & M. Kolountzakis, "Tiling, spectrality and aperiodicity of connected sets,"
[arXiv:2305.14028](https://arxiv.org/abs/2305.14028), *Israel J. Math.*** From an aperiodic tile
F ⊂ ℤ^d they build **(d + 2)-dimensional "folded bridges"** between F's connected components, preserving
aperiodicity. Hence a **connected** single tile that tiles ℤ^n (and ℝ^n) **only aperiodically by
translations** exists in sufficiently high dimension. (They also kill both directions of Fuglede's
conjecture for connected sets.)

> **Status: PROVEN.** Connectivity is *not* an obstruction in high dimension — but the construction still
> needs **+2 dimensions** and gives nothing at small d.

### 4.4 Decidability: undecidability of translational **monotiling** (dimension as input) ★

**R. Greenfeld & T. Tao, "Undecidability of translational monotilings,"
[arXiv:2309.09504](https://arxiv.org/abs/2309.09504) (Sept 2023)
([Tao's blog](https://terrytao.wordpress.com/2023/09/18/undecidability-of-translational-monotilings/)).**

> **Theorem (Greenfeld–Tao 2023).** There is **no algorithm** that, given a dimension d, a **periodic**
> subset E ⊆ ℤ^d, and a finite F ⊆ ℤ^d, decides whether there exists A with **A ⊕ F = E** (translational
> tiling of E by the single tile F). Equivalently, monotiling of periodic subsets of "virtually-ℤ²" groups
> **ℤ² × G₀** (G₀ finite abelian) is undecidable, and hence **monotiling of ℤ^d is undecidable when the
> dimension d is part of the input.**

Crucial qualifiers:

- It is about tiling a **periodic subset E**, not necessarily all of ℤ^d (a noted technical limitation).
- It is the **monotile** (single-tile) translational problem — by far the hardest such undecidability to
  obtain.
- **OPEN: decidability at any fixed d > 2.** Tao/Greenfeld: *"It remains open whether the tiling problem is
  decidable for any fixed value of d > 2."* In d = 2 it is **decidable** (Bhattacharya's PTC ⇒ a periodic
  tiling can be searched for and certified).

> **The standing conjecture (Greenfeld–Tao):** there is **some fixed dimension n** for which **translational
> monotiling of ℤ^n is undecidable** — which would, by the Berger logic, *force* a fixed-dimension
> translational aperiodic monotile. Their dimension-as-input result is the strongest current evidence.

### 4.5 The fixed-dimension tile-set frontier (rapidly moving, 2024–2025)

Independently of the *monotile* question, the **fixed-dimension tile-SET** translational undecidability has
been pushed down fast (these are **PROVEN**, translation-only, by Chao Yang & Zhujun Zhang and others):

- ℤ² with **8 tiles** undecidable (earlier baseline).
- ℤ³ with **6 polycubes** — [arXiv:2408.02196](https://arxiv.org/abs/2408.02196) (Yang–Zhang, Aug 2024).
- ℤ³ with **5 polycubes**, and ℤ⁴ with **4 polyhypercubes** (lift 3D→4D) —
  [arXiv:2409.00846](https://arxiv.org/abs/2409.00846), *Science China Math.* 68 (2025) 2173–2188.
- ℤ³ with **3 polycubes** — [arXiv:2508.00192](https://arxiv.org/abs/2508.00192) (Yang–Zhang, Jul 2025).
- ℤ³ with **2 polycubes** — [arXiv:2508.11725](https://arxiv.org/abs/2508.11725) (Aug 2025) — *verify, very recent.*
- (Plane, isometries) **tiling with 3 polygons** undecidable — Demaine–Langerman
  [arXiv:2409.11582](https://arxiv.org/pdf/2409.11582).

> **Status: PROVEN (multi-tile).** The number of tiles needed for *undecidable translational tiling in a
> fixed low dimension* is collapsing toward 1. The last step — **one tile** at fixed d — is the open
> Greenfeld–Tao conjecture (§4.4). The technique throughout: a subshift embedding **universal computation**,
> with extra dimensions used to **control/forbid periodicity** (the 3D extra coordinates play exactly the
> role of Berger's aperiodic scaffold).

### 4.6 What Greenfeld–Tao DOES and DOES NOT say about a geometric strongly-aperiodic 3D monotile

| It DOES | It DOES NOT |
|---|---|
| Prove a **single translational** aperiodic tile exists in **some fixed (huge) dimension**. | Give any tile at **d = 3** (Greenfeld *doubts* 3D; thinks **4D** plausible). |
| Allow the tile to be **connected** (Greenfeld–Kolountzakis), at the cost of +2 dimensions. | Say anything about **rotations/screws** — it is **translations only**, so "strong aperiodicity (no infinite cyclic symmetry)" is **not** its notion; the relevant ℤ^d notion is "no nonzero **translation** period," which it *does* achieve. |
| Make monotiling **undecidable with dimension as input**; conjecture a **fixed-d** undecidability. | Resolve decidability at **any fixed d > 2** (open), or settle the **geometric 𝔼³ einstein** (question C). |
| Supply the modern **"almost no local rule lifts"** mechanism (functional equations, Sudoku, undecidability). | Supply a **shape** whose **isometry** symmetry group is forced trivial-up-to-finite (the 𝔼³ strong-aperiodicity target). |

> **Reading for us:** Greenfeld–Tao is the **decidability/forcing skeleton** for the *translational* π₀ in
> 3D — it tells us the *translational* monotile problem is (conjecturally) **undecidable at a fixed d**, i.e.
> the strongest possible "rarity." It is **not** a recipe for a geometric strongly-aperiodic 3D solid, and
> Greenfeld's own intuition is that d = 3 is **too small** for the translational version.

---

## 5. (Group-theoretic monotiles) — aperiodicity as a property of a subset of a group

The cleanest unifying language — and the one that puts (B), (C), (D) on a common footing — is to forget
geometry and ask about a **subset T of a group G** that **tiles G** (left translates partition G) only
**aperiodically**.

### 5.1 The framing (Coulbois–Gajardo–Guillon–Lutfalla 2024) ★

**T. Coulbois, A. Gajardo, P. Guillon, V. Lutfalla, "Aperiodic monotiles: from geometry to groups,"
[arXiv:2409.15880](https://arxiv.org/abs/2409.15880) (2024).** They reformulate aperiodicity as a property
of **group actions**: a monotile T ⊆ G tiles modulo the action of its **stabilizer (symmetry group)**, and
periodicity means a nontrivial g ∈ G fixes the tiling. The standard group-theoretic dichotomy
([generalizing Goodman-Strauss; cf. Cohen, Goodman-Strauss, Rieck and the "domino on groups" literature](https://link.springer.com/chapter/10.1007/978-3-030-57666-0_6)):

> - **Weakly aperiodic (group version):** every tiling has **finite-index** stabilizer is *forbidden*, i.e.
>   no tiling is fixed by a *finite-index* subgroup (no "fully periodic" tiling), **but** an infinite cyclic
>   subgroup may still act (the screw-axis case).
> - **Strongly aperiodic (group version):** every tiling has **trivial** stabilizer — **no nontrivial**
>   g ∈ G fixes any tiling (no infinite-order symmetry at all).

This reproduces, with no metric, the SCD/Socolar–Taylor situation: those 3D monotiles are *weakly* but not
*strongly* aperiodic because the screw / layer-shift is an **infinite cyclic** subgroup of Isom(𝔼³).

### 5.2 How the geometric 3D problem maps in

- **𝔼³ einstein (C)** ⟷ monotile in **G = Isom(ℝ³)** (or a crystallographic supergroup): "strongly
  aperiodic" = trivial stabilizer for every tiling, which **bans screws** — the open problem.
- **Translational 3D (D)** ⟷ monotile in **G = ℤ³** (or ℝ³ under translations only): here the only possible
  periods are translations, so "weak = strong" collapses and the relevant question is the
  **Greenfeld–Tao** one. Their ℤ² × G₀ counterexample is literally "a monotile in a virtually-ℤ² group."
- **The icosahedral matching tiles (B)** ⟷ a finite generating set (not a single element) of a
  ℤ⁶-decorated SFT projecting to ℝ³ — the projection bridge, not a group-monotile.

> **Why this helps the program:** the group-theoretic picture is *exactly our "shadow of a higher layer"*
> in algebraic clothes — the higher layer is the **ambient group G** (e.g. ℤ⁶ or Isom(𝔼³)) and the tile is
> a **fundamental-domain-like subset** whose admissible translates are the SFT. **Strong aperiodicity =
> trivial stabilizer of every lift**, which is the group-theoretic statement of our **non-descending /
> strict-extension** certificate. It also makes the **screw axis** (the 3D obstruction) visible as a
> specific **infinite-cyclic subgroup that survives the descent** — precisely the failure mode our F8
> fiber-collision audit should be tuned to detect in 3D.

---

## 6. The 3D rarity / forcing synthesis — is there a 3D analogue of (Le) + (Hochman–Meyerovitch) + (Berger)?

The 2D rarity engine of [../06_matching_rules_SFT_decidability.md §6](../06_matching_rules_SFT_decidability.md)
rests on three independent legs. **All three transfer to 3D — and a fourth, sharper leg (Greenfeld–Tao)
is available.** This is the central deliverable of this dossier.

### Leg 1 — Le's algebraic obstruction is *dimension-general* (projection side) ★

Le's 1997 theorem ("slope admits weak local rules ⇒ slope is algebraic") is stated for slopes in an
**arbitrary** Grassmannian G(n, d), so it applies verbatim to **3-planes in ℝ⁶ (icosahedral) and to all
higher-codimension 3D cut-and-project schemes**. The slopes form a **continuum (a real Grassmannian)**; the
slopes admitting any finite local rule are confined to the **countable, measure-zero algebraic locus**
(conjecturally **quadratic** for the low-codimension cases, by the Le/Bédaride–Fernique pattern).

> **3D rarity, projection side:** *almost every 3D projection direction is **un-enforceable** by any finite
> matching rule.* A local observer can be compelled into a 3D quasicrystalline higher layer **only** at
> algebraic/quadratic slopes — the icosahedral golden-ratio slope being the distinguished forceable point.
> This is identical in spirit to the 2D statement; **no new theorem is required**, only the observation that
> Le is dimension-general. ([Le 1997; Bédaride–Fernique, arXiv:1812.06863](https://arxiv.org/pdf/1812.06863).)

*Caveat / open edge:* the **effective** Bédaride–Fernique coincidence/Plücker criterion (necessary *and
sufficient*, decidable) is proved for **codimension-2 rhombus tilings** (2-planes in ℝ⁴); a fully analogous
*effective* characterization for the **icosahedral codimension-3** case is, to our knowledge, **not written
down in the same closed form** — worth flagging as a concrete sub-question.

### Leg 2 — Hochman–Meyerovitch holds for **all** d ≥ 2 (SFT-counting side) ★

**Hochman–Meyerovitch (Annals 2010):** for **multidimensional** SFTs (ℤ^d, **d ≥ 2**), the achievable
entropies are *exactly* the non-negative **right-recursively-enumerable** reals — locally-admissible counts
converge to the true entropy **from above**, with a genuine uncomputable gap; an *irreducible* SFT has
computable entropy. ([arXiv:math/0703206](https://arxiv.org/abs/math/0703206);
[Annals PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p12-p.pdf).)

> **3D rarity, SFT side:** the result is *stated for every d ≥ 2*, so the **quantitative SFT ⊊ sofic gap**
> — the from-above, uncomputable shortfall between locally-legal counts and true entropy — is **already a
> 3D theorem**. Our "the local layer under-determines the global hierarchy" claim is *exactly* this gap in
> ℤ³. **No 3D-specific work needed.**

### Leg 3 — Berger/undecidability is *even stronger* in 3D (computational side) ★

Domino-problem undecidability holds for **all ℤ^d, d ≥ 2** (§1), and the **fixed-dimension translational**
undecidability frontier is collapsing toward a single tile (§4.5). So the computational-rarity leg is
**at least as strong** in 3D as in 2D, and on the translational-monotile question is **conjecturally
sharper** (a *fixed-dimension* undecidability, vs the 2D *decidable* monotile case).

### Leg 4 (NEW in high-d) — Greenfeld–Tao: undecidability of **monotiling** itself ★

In 2D the *monotile* translational problem is **decidable** (Bhattacharya). The high-dimensional novelty is
that for **single tiles** the problem becomes **undecidable with dimension as input** (§4.4), and is
**conjectured undecidable at a fixed dimension**. This is a *strictly stronger* rarity statement than
anything available in 2D: it says **even after collapsing to one tile**, no algorithm can certify the lift.

### The synthesis statement (for our forcing/π₀ argument in 3D)

> **3D rarity, assembled.** Among 3D local rules / candidate π₀'s:
> 1. **(Le, dimension-general)** only an **algebraic/quadratic, measure-zero** set of projection slopes is
>    *enforceable at all* — almost no slope admits a consistent cut-and-project lift;
> 2. **(Hochman–Meyerovitch, d ≥ 2)** even among enforceable structures, locally-legal configurations
>    **over-count** the truly-global ones by an **uncomputable** margin (SFT ⊊ sofic) — the local layer
>    genuinely under-determines the hierarchy in ℤ³;
> 3. **(Berger, all d ≥ 2; Greenfeld–Tao, monotiles)** there is **no algorithm** to decide tileability in
>    general, and (conjecturally) **not even for a single tile at fixed dimension** — so "does this π₀ admit
>    a consistent lift?" is, in the worst case, **formally undecidable**.
>
> Together these are the 3D form of Foundations I's **Finite Forcing Lemma**: a generic 3D local rule
> **almost never** admits a consistent hierarchical/projection lift, by a **measure-zero** (number-theoretic)
> argument, an **uncomputable-gap** (entropy) argument, **and** an **undecidability** (computational)
> argument — three independent ceilings, the same trident as 2D, **plus** a sharper translational-monotile
> ceiling unique to high dimension.

*Honesty caveat:* Legs 1–3 are **direct ports** (the underlying theorems are dimension-general or
explicitly d ≥ 2); the 3D content is the *observation* that they transfer, not new theorems. Leg 4 is
genuinely high-dimensional but concerns **translations only** and a **huge/abstract** dimension, so it
constrains the *translational* π₀, not directly the **geometric isometry** π₀ of question (C).

---

## 7. Relevance to our shadow / strict-extension approach

**How forcing / π₀ works in 3D.** Our π₀ is the **local matching-rule SFT** (or, in the hat-style ideal,
the bare shape-adjacency SFT); π₁ is the **higher cut-and-project / substitution layer**. The 3D evidence
sorts cleanly against our certificate:

1. **The SFT layer CAN be strongly aperiodic in 3D (§1), and CAN force the icosahedral higher layer (§2).**
   So for **tile sets**, the π₀ → π₁ forcing our program needs is a **solved, classical fact** in 3D —
   Katz/Socolar are an existing positive instance of "audited descent from a higher periodic layer (ℤ⁶) to
   a 3D shadow." Re-deriving Katz (two Ammann rhombohedra, golden/√5 slope = our distinguished quadratic
   (λ, W)) is the natural **3D analogue of re-deriving the hat / Ammann–Beenker** before walking to an
   unrealized shadow.

2. **The strict-extension certificate has a sharp 3D meaning: trivial stabilizer of every lift (§5).** In
   the group-theoretic language, **strong aperiodicity = no infinite-cyclic symmetry survives the descent**.
   The **specific 3D failure mode** our F8 fiber-collision audit must catch is the **screw axis / periodic
   layer-shift** — the exact gap by which SCD and Socolar–Taylor are only *weakly* aperiodic. **Concretely:
   in 3D the audit must certify not just "no translation period" but "no surviving infinite-cyclic symmetry
   (no screw)."** This is a genuine, stateable upgrade to the certificate for the 3D setting.

3. **The rarity/forcing lemma transfers (§6)** — the trident (Le measure-zero + Hochman–Meyerovitch
   from-above + Berger undecidability) is dimension-general/d ≥ 2, so "almost no 3D local rule admits a
   consistent lift" is supported with the *same* strength as 2D. This is a **port, not a new theorem** —
   keep that honest.

**Is Greenfeld–Tao a route or a warning? — Both, and we should use it as both.**

- **As a route (method, not object):** their **functional-equation / Sudoku** encoding is a concrete *recipe*
  for "a single tile whose only admissible lifts are aperiodic," realized through a **decorated finite-group
  factor (ℤ² × G₀)**. That decorated-factor trick is *structurally our "audited shadow of a higher layer"*:
  the finite group G₀ is a tiny periodic upstairs that forces aperiodicity downstairs by translations.
  **If a strongly-aperiodic 3D *isometry* monotile is to be engineered, the Greenfeld–Tao "encode functional
  equations as one tiling equation" template is the most promising algebraic engine to adapt** — replacing
  "translations on ℤ² × G₀" by "isometries on a crystallographic group with a screw-free constraint."

- **As a warning (three red flags):**
  1. **Dimension.** Their construction is "as low as the method reaches" and still lands at astronomically
     high d; **Greenfeld herself doubts d = 3** and only guesses **4D** is plausible. So the Greenfeld–Tao
     *object* is **not** a 3D monotile and gives **no** d = 3 construction — chasing it directly is likely a
     dimensional dead end for a *geometric 3D* tile.
  2. **Translations only.** It says nothing about killing **screws**, which is the *entire* 3D difficulty
     (question C). A translational counterexample is the *easy* notion in ℤ³; the hard, open notion is the
     **isometry** one.
  3. **Undecidability is a barrier to *search*, not a tile.** Greenfeld–Tao monotiling-undecidability (and
     the conjectured fixed-d version) means a naive **"enumerate shapes, test for forced aperiodicity"**
     hunt for a 3D einstein can be **non-terminating in the worst case** — which is *why* our program's
     **heuristic-walk + exact-verifier over already-realized shadows** (re-derive Katz, then walk the
     quadratic/icosahedral (λ, W) family) is the right shape: it stays inside the **decidable, algebraic,
     Le-enforceable** locus instead of brute-forcing the undecidable general problem.

**Net recommendation for the 3D move.** Treat **(B) Katz/Socolar icosahedral matching rules** as the 3D
proof-of-concept to re-derive (golden/√5 slope, ℤ⁶ ↓ ℝ³); treat **(C) the strongly-aperiodic 3D einstein**
as the genuine open prize whose certificate upgrade is **"trivial stabilizer / no surviving screw"**; mine
**(D) Greenfeld–Tao's functional-equation/finite-group-factor method** as the **algebraic engine** for
forcing aperiodicity from a small periodic upstairs — while heeding its warning that the *general* and
*translational-monotile* problems are undecidable / dimensionally explosive, so we must hunt **inside the
algebraic-slope (Le) island**, not in the open sea.

---

## Authoritative sources (titles + URLs)

**(A) Domino problem & strongly-aperiodic SFTs in 3D**
- E. Jeandel, P. Vanier, *The Undecidability of the Domino Problem* — [Springer chapter](https://link.springer.com/chapter/10.1007/978-3-030-57666-0_6); [survey PDF](https://www.lacl.fr/pvanier/rech/cirm.pdf)
- R. Robinson, *Undecidability and nonperiodicity for tilings of the plane*, Invent. Math. 12 (1971) — [PDF](https://users.cs.duke.edu/~reif/courses/molcomplectures/TilingAssembly/TilingComputability/UndecidabilityTilingRobinson.pdf)
- S. Mozes, *Aperiodic tilings* / strongly aperiodic tile sets on symmetric spaces (Lie groups), J. Anal. Math. 1997 — (via [Einstein problem, Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem))

**(B) 3D icosahedral matching rules (the projection bridge in 3D)**
- A. Katz, *Theory of matching rules for the 3-dimensional Penrose tilings*, CMP 118 (1988) 263–288 — [Springer](https://link.springer.com/article/10.1007/bf01218580)
- J. Socolar, *Weak matching rules for quasicrystals*, CMP 129 (1990) 599 — [Springer](https://link.springer.com/article/10.1007/BF02097107)
- L. Levitov, *Local rules for quasicrystals*, CMP 119 (1988) 627 — [Project Euclid PDF](https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-119/issue-4/Local-rules-for-quasicrystals/cmp/1104162600.pdf)
- T.T.Q. Le, *Local rules for quasiperiodic tilings*, NATO ASI C-489, Kluwer 1997, pp. 331–366 (the dimension-general algebraic obstruction)
- T.T.Q. Le, S. Piunikhin, V. Sadov, *Local rules for quasiperiodic tilings of quadratic 2-planes in ℝ⁴*, CMP 1995 — [Springer](https://link.springer.com/article/10.1007/BF02096563); Le–Piunikhin–Sadov, CMP 1992 — [Springer](https://link.springer.com/article/10.1007/BF01218348)
- N. Bédaride, T. Fernique, *Canonical projection tilings defined by patterns*, Geom. Dedicata 2020 — [arXiv:1812.06863](https://arxiv.org/abs/1812.06863)
- *Robust minimal matching rules for quasicrystals* — [arXiv:1809.10614](https://arxiv.org/abs/1809.10614)
- *Substitution rules for icosahedral quasicrystals*, RSC Adv. 2015 — [RSC](https://pubs.rsc.org/en/content/articlehtml/2015/ra/c4ra09524c)

**(C) The single geometric 3D tile (3D einstein); weak vs strong aperiodicity**
- Einstein problem — [Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem)
- Schmitt–Conway–Danzer biprism — [Polytope Wiki](https://polytope.miraheze.org/wiki/Schmitt%E2%80%93Conway%E2%80%93Danzer_biprism)
- J. Socolar, J. Taylor, *Forcing nonperiodicity with a single tile*, Math. Intelligencer 34 (2012) 18–28 — [arXiv:1009.1419](https://arxiv.org/pdf/1009.1419); [Socolar–Taylor tile, Wikipedia](https://en.wikipedia.org/wiki/Socolar%E2%80%93Taylor_tile)
- C. Kaplan, *The Path to Aperiodic Monotiles* — [arXiv:2509.12216](https://arxiv.org/pdf/2509.12216); [Isohedral: Aperiodic Monotiles](https://isohedral.ca/aperiodic-monotiles/)
- *Now that's what I call an aperiodic monotile!* — [The Aperiodical](https://aperiodical.com/2023/05/now-thats-what-i-call-an-aperiodic-monotile/)

**(D) Greenfeld–Tao: PTC, connectivity, undecidability of monotilings; fixed-d frontier**
- R. Greenfeld, T. Tao, *A counterexample to the periodic tiling conjecture* — announcement [arXiv:2209.08451](https://arxiv.org/abs/2209.08451); full [arXiv:2211.15847](https://arxiv.org/abs/2211.15847); Annals 200(1) (2024) — [journal](https://annals.math.princeton.edu/2024/200-1/p05); [Tao's blog](https://terrytao.wordpress.com/2022/09/19/a-counterexample-to-the-periodic-tiling-conjecture/)
- *'Nasty' Geometry Breaks Decades-Old Tiling Conjecture* — [Quanta Magazine](https://www.quantamagazine.org/nasty-geometry-breaks-decades-old-tiling-conjecture-20221215/)
- R. Greenfeld, M. Kolountzakis, *Tiling, spectrality and aperiodicity of connected sets*, Israel J. Math. — [arXiv:2305.14028](https://arxiv.org/abs/2305.14028)
- R. Greenfeld, T. Tao, *Undecidability of translational monotilings* — [arXiv:2309.09504](https://arxiv.org/abs/2309.09504); [Tao's blog](https://terrytao.wordpress.com/2023/09/18/undecidability-of-translational-monotilings/)
- C. Yang, Z. Zhang, *Undecidability of translational tiling of ℤ³ with 6 polycubes* — [arXiv:2408.02196](https://arxiv.org/abs/2408.02196)
- C. Yang, Z. Zhang, *…ℤ³ with 5 / ℤ⁴ with 4 polyhypercubes*, Sci. China Math. 68 (2025) — [arXiv:2409.00846](https://arxiv.org/abs/2409.00846)
- C. Yang, Z. Zhang, *On the undecidability of tiling ℤ³ with 3 polycubes* — [arXiv:2508.00192](https://arxiv.org/abs/2508.00192)
- *Undecidability of translational tiling of ℤ³ with 2 polycubes* — [arXiv:2508.11725](https://arxiv.org/abs/2508.11725) *(very recent; verify)*
- E. Demaine, S. Langerman, *Tiling with three polygons is undecidable* — [arXiv:2409.11582](https://arxiv.org/pdf/2409.11582)

**(Group-theoretic monotiles)**
- T. Coulbois, A. Gajardo, P. Guillon, V. Lutfalla, *Aperiodic monotiles: from geometry to groups* — [arXiv:2409.15880](https://arxiv.org/abs/2409.15880)

**(Rarity engine, dimension-general)**
- M. Hochman, T. Meyerovitch, *A characterization of the entropies of multidimensional shifts of finite type*, Annals 171(3) (2010) 2011–2038 — [arXiv:math/0703206](https://arxiv.org/abs/math/0703206); [Annals PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p12-p.pdf)

---

## Status flags (PROVEN / OPEN, with dates)

- **PROVEN (1966–71, all d ≥ 2):** domino problem undecidable on ℤ^d ⇒ strongly-aperiodic *tile sets* exist in 3D (Berger, Robinson; Mozes 1997 on Lie groups).
- **PROVEN (1988–90):** finite *matching rules* force the 3D **icosahedral** quasicrystal — **weak** rules (Socolar 1990; Levitov 1988), via Ammann-plane decorations of the two rhombohedra (Katz 1988).
- **PROVEN dimension-general (Le 1997):** enforceable slopes are **algebraic** (measure-zero); quadratic suffices in low codimension (Le–Piunikhin–Sadov; Bédaride–Fernique).
- **PROVEN (1988 / 2012):** a single *geometric* 3D monotile that never tiles periodically exists — **SCD** (convex) and **Socolar–Taylor** (connected) — but both are only **WEAKLY aperiodic** (screw axis / periodic layer-shift).
- **OPEN (as of 2026):** a **strongly-aperiodic 3D monotile** (no surviving infinite-cyclic / screw symmetry); and any **shape-only, decoration-free** 3D "hat."
- **PROVEN (Greenfeld–Tao 2022/Annals 2024):** the periodic tiling conjecture is **FALSE** in sufficiently large dimension — a **single translational** aperiodic tile exists (ℤ² × G₀; disconnected by default; d astronomically large).
- **PROVEN (Greenfeld–Kolountzakis):** that counterexample can be made **connected** (+2 dimensions).
- **PROVEN (Greenfeld–Tao 2023):** translational **monotiling** is **undecidable with dimension as input**.
- **OPEN:** decidability of translational tiling at **any fixed d > 2** (decidable at d = 2, Bhattacharya); whether a **fixed-dimension** translational aperiodic monotile / undecidability exists (conjectured **yes**); whether a translational aperiodic monotile exists at **d = 3** (Greenfeld conjectures **no**; **4D** plausible).
- **PROVEN & moving fast (2024–25):** fixed-dimension *tile-set* translational undecidability — ℤ³ with **6 → 5 → 3 → (2, verify)** polycubes; ℤ⁴ with **4** polyhypercubes.
