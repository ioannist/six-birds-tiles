# Geometric realizability of matching rules on a SINGLE 3D tile — the no-smuggling gate

*Focused dossier compiled June 2026 from primary sources (arXiv, Project Euclid, Annals, Baake–Frettlöh, Socolar–Taylor, Kaplan, Wikipedia). Every load-bearing claim is tagged **[CITED]** (with URL) or **[INFERRED]** (my synthesis from cited facts). Read companion files [`01_3d_problem_scd.md`](01_3d_problem_scd.md) and [`04_3d_forcing_decidability_group.md`](04_3d_forcing_decidability_group.md) first — they cover SCD geometry and the SFT/forcing layer in depth; this file is the dedicated treatment of **whether octahedral / decoration matching rules can collapse onto one connected solid in 3D**.*

---

## 0. The question, sharpened

The **no-smuggling gate**: an aperiodic tiling forced by **matching rules** (decorations / colored facets / bumps–notches / Ammann-plane continuity) is only an honest *single-tile* result if those rules can be **realized geometrically on one connected solid** (a tile whose *shape alone*, modulo isometry, enforces the rule). The alternatives — (i) ≥2 prototiles, (ii) non-geometric color labels, (iii) a *disconnected* "tile" — each defeat the claim of a true monotile.

The headline finding, established below from primary sources, is a clean **dimensional dichotomy**:

> **[CITED+INFERRED]** In **2D**, the Socolar–Taylor matching rule provably *cannot* be encoded in a simply-connected disk (it references **non-adjacent** tiles), so the shape-only realization is **disconnected**. In **3D**, the extra dimension **does** let that exact rule be absorbed into a **single simply-connected solid by shape alone (no color)** — but the resulting tiling is only **weakly aperiodic** (a 2D-periodic slab stacked periodically). So geometric absorption of matching rules onto one connected 3D tile is **demonstrated** (Socolar–Taylor); what remains **open** is doing so while reaching **strong** aperiodicity.

There is, as of June 2026, **no published impossibility theorem** forbidding a strongly aperiodic single (connected, even unmarked) tile in ℝ³. The hardness is "no construction + daunting verification," not a proven obstruction.

---

## 1. SOCOLAR–TAYLOR in 3D — the central case

### 1.1 The papers (primary sources)

- **[CITED]** J. E. S. Socolar & J. M. Taylor, *"An aperiodic hexagonal tile,"* **J. Combin. Theory Ser. A 118 (2011) 2207–2231**; arXiv preprint **1003.4279** — [arXiv:1003.4279](https://arxiv.org/abs/1003.4279). The combinatorial/substitution paper.
- **[CITED]** J. E. S. Socolar & J. M. Taylor, *"Forcing nonperiodicity with a single tile,"* **The Mathematical Intelligencer 34 (2012), no. 1, 18–28**; arXiv **1009.1419** — [arXiv:1009.1419](https://arxiv.org/abs/1009.1419), readable HTML at [ar5iv](https://ar5iv.labs.arxiv.org/abs/1009.1419). This is the paper with the 2D-shape and 3D-shape constructions and the explicit 3D-tile figures. *(Note: secondary sources sometimes swap the two titles/venues; the 1009.1419 preprint is the one carrying the geometric-realization discussion.)*

### 1.2 The 2D tile: the rule R2 is non-local ⇒ shape-only is DISCONNECTED

The Socolar–Taylor hexagon carries **two** matching rules. **[CITED]** The obstruction to a connected shape-only 2D tile is stated outright:

> *"R2 necessarily refers to tiles that are not in contact in the tiling and R1 cannot be implemented using only the shape of a single prototile and its mirror image."* — [Socolar–Taylor, arXiv:1009.1419](https://ar5iv.labs.arxiv.org/abs/1009.1419)

R2 is a **next-nearest-neighbour** constraint (it constrains a tile and one two cells away, *across* an intervening tile). Because boundary contact only transmits information between *adjacent* tiles, a simply-connected disk cannot carry it. Their shape-only 2D realization is therefore an explicitly **disconnected** figure:

> *"Figure 6(a) shows how the color–matching rules can be encoded in the shape of a single prototile that consists of several disconnected regions. In the figure, all regions of the same color are considered to compose a single tile."* — [Socolar–Taylor, arXiv:1009.1419](https://ar5iv.labs.arxiv.org/abs/1009.1419) **[CITED]**

So the "single tile" in 2D-shape form is a **union of separated islands declared to be one tile** — i.e. it cheats the no-smuggling gate exactly the way (iii) above describes. (A variant joins the islands only **through vertices / cutpoints**, which is connected-but-not-a-disk; **[CITED]** Wikipedia summarizes the result and notes it remains *"unknown whether this rule may be geometrically implemented in two dimensions while keeping the tile a simply connected set"* — [Socolar–Taylor tile, Wikipedia](https://en.wikipedia.org/wiki/Socolar%E2%80%93Taylor_tile).)

> **[INFERRED]** This is the cleanest known *demonstration* that, in a fixed dimension, a genuine matching rule can be **provably unembeddable** in a connected disk — the rule's range exceeds adjacency. It is the canonical example motivating the no-smuggling gate.

### 1.3 The 3D tile: the rule IS absorbed into ONE SIMPLY-CONNECTED solid, by SHAPE ALONE

The dimensional payoff: lift to 3D and the non-adjacent 2D constraint becomes an *adjacent* 3D constraint (the missing channel is routed through the third dimension). **[CITED]**, verbatim:

> *"Thus we see that matching rules equivalent to those of the 2D tile can be enforced by the shape of a simply connected three–dimensional prototile."* — [Socolar–Taylor, arXiv:1009.1419](https://ar5iv.labs.arxiv.org/abs/1009.1419)

and the decorations are explicitly **not needed** — pure geometry suffices:

> *"The colored bars running through the 3D tile are guides to the eye that display the black and purple stripe structure, but they are not required. The continuity of the bars is enforced by the shape of the tile alone."* — [Socolar–Taylor, arXiv:1009.1419](https://ar5iv.labs.arxiv.org/abs/1009.1419) **[CITED]**

So **"monotile" here means: one connected, simply-connected, UNmarked solid** whose bumps/notches/bevels encode the rule. This is a real, positive answer to the gate's core question *in the weak regime*.

### 1.4 …but it is only WEAKLY aperiodic (periodic stacking)

The catch is the price of the dimensional trick. **[CITED]**:

> *"The space–filling tiling forced purely by the shape of this tile consists of a corrugated slab isomorphic to the structure forced by the 2D tiles … which may be stacked periodically to fill the 3D space."* — [Socolar–Taylor, arXiv:1009.1419](https://ar5iv.labs.arxiv.org/abs/1009.1419)

The tile forces a single aperiodic 2D layer, but copies of that layer **stack with a translation period** along the normal. The 3D tiling is therefore **periodic in one direction** → **weakly aperiodic**, not strongly aperiodic. **[CITED]** Wikipedia: the 3D tile *"allows tilings with a period, shifting one (non-periodic) two dimensional layer to the next … the tile is only 'weakly aperiodic'"* — [Socolar–Taylor tile, Wikipedia](https://en.wikipedia.org/wiki/Socolar%E2%80%93Taylor_tile). (Socolar–Taylor still call it *non-periodic* by their own definition because the layer has *"complex correlations over large scales,"* but it admits an infinite cyclic translation symmetry — the disqualifier for *strong* aperiodicity.) **[CITED]**

> **[INFERRED]** Net for the gate: Socolar–Taylor **settle the connected/unmarked-realizability question affirmatively in the weak regime** and **expose the precise trade**: the third dimension is *spent* routing the long-range channel, leaving a residual periodic stacking. Strong aperiodicity would require *also* killing that stacking symmetry — the open part.

---

## 2. DANZER ABCK — "perfect local rules on the level of the octahedra"

### 2.1 The original source

- **[CITED]** L. Danzer, *"Three-dimensional analogs of the planar Penrose tilings and quasicrystals,"* **Discrete Mathematics 76 (1989) 1–7** — [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0012365X89902823). This is the origin of the **four tetrahedral prototiles A, B, C, K** ("ABCK"). Further development: **L. Danzer, Z. Papadopolos & A. Talis**, *"Full equivalence between Socolar's tilings and the (A,B,C,K)-tilings,"* **Int. J. Mod. Phys. B 7 (1993)**. **[CITED]** (refs collected in [Frettlöh–Baake "ikosa"](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf) and [Koca et al., Symmetry 12 (2020) 1983](https://www.mdpi.com/2073-8994/12/12/1983)).

### 2.2 The prototiles, octahedra, and inflation (exact)

**[CITED]** (Zerhusen / Univ. Kentucky exposition of Danzer's tiling — [ms.uky.edu/~lee/zerhusen/quasi.html](https://www.ms.uky.edu/~lee/zerhusen/quasi.html); cross-checked against [Frettlöh–Baake ikosa](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf)):

- **4 prototiles**: skew tetrahedra **A, B, C, K**. Vertices labeled 1–4.
- Edges fall in **three classes** ("red, white, green"), all lengths **multiples of the golden ratio τ** (red = τⁿ; white = (cos 18°)τⁿ; green = (cos 30°)τⁿ).
- **Octahedra**: tiles **A, B, C each assemble into an octahedron of 4 copies**; tile **K into an octahedron of 8 copies** (two concave "dart" octahedra, two convex "kite" octahedra). **[CITED]**
- **Inflation factor τ** (golden ratio); self-similar substitution generates the infinite tiling. **[CITED]**
- **Cut-and-project**: ABCK vertices project from the **D6 / ℤ⁶** root lattice; the tiling is **mutually locally derivable from the Socolar–Steinhardt 1986 rhombohedral tiling**. **[CITED]** ([Koca et al. 2020, Symmetry](https://www.mdpi.com/2073-8994/12/12/1983); search-confirmed).

### 2.3 The "perfect local rules on the octahedra" claim — statement and attribution

The exact claim the user asked for, verbatim as it circulates in the Bielefeld/Baake literature (the standard reference phrasing):

> *"An interesting property of Danzer's ABCK tiling is the fact that it possesses particularly simple **perfect local rules, which can be formulated as purely geometric packing rules on the level of the octahedra**."* — phrasing from [Frettlöh–Baake, "Icosahedral tilings in ℝ³: the ABCK tilings"](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf) and repeated in the diffraction literature [arXiv:1205.3633](https://arxiv.org/abs/1205.3633). **[CITED]** (text retrieved via search excerpt of the Bielefeld PDF; the arXiv PDFs would not render to text in-tool, so the *verbatim* string is from the indexed excerpt, not a clean fetch — flagged.)

**What "perfect" means.** **[CITED+INFERRED]** In the Baake–Grimm vocabulary, **"perfect local rules"** = a finite set of *local* (matching) conditions whose **every** globally-admissible tiling lies in the desired (substitution/model-set) hull — i.e. the rules **force exactly** the ABCK quasicrystal, with **no spurious admissible tilings**. This is the *strong*-matching-rule property (contrast Levitov/Socolar **weak** rules, which only force it up to bounded defects). Reference framing: **M. Baake & U. Grimm, *Aperiodic Order, Vol. 1: A Mathematical Invitation*, CUP 2013** — [CUP](https://www.cambridge.org/core/books/abs/aperiodic-order/more-inflation-tilings/1D706353EF4545718A3792A2102677AB). **[CITED]**

**Who proved it / where.** **[INFERRED, with caveat]** The perfect-rule property for ABCK is **Danzer's own program** (Danzer 1989; Danzer–Papadopolos–Talis 1993), with the octahedral reformulation and the rigorous local-rules ↔ Ammann-plane equivalence developed in the **Baake–Frettlöh–Gähler** circle (the canonical exposition is the Bielefeld "ikosa" notes + *Aperiodic Order* Vol. 1). I could **not** isolate a single standalone "perfect matching rules for ABCK, Theorem X" paper with a clean in-tool fetch (the arXiv PDFs failed to render and the MDPI/ResearchGate pages returned HTTP 403). **The rigorous matching-rules technology it rests on is Katz's** (next item). Treat the precise *proof attribution* as **needs-one-more-fetch** (the Bielefeld ikosa PDF or *Aperiodic Order* §5–6 will give the citation chain).

### 2.4 The rigorous engine underneath: Katz 1988 (Ammann-rhombohedra Penrose, 3D)

- **[CITED]** A. Katz, *"Theory of matching rules for the 3-dimensional Penrose tilings,"* **Commun. Math. Phys. 118 (1988) 263–288** — [Project Euclid](https://projecteuclid.org/euclid.cmp/1104161989), [Springer](https://link.springer.com/article/10.1007/BF01218580). He takes the **two Ammann rhombohedra**, **decorates their facets**, and **proves any tiling respecting the matching decorations is a quasiperiodic 3D Penrose (icosahedral) tiling** — *"The proof does not involve any reference to self-similarity."* **[CITED]**
- **[CITED]** Weak-rule companions: **L. S. Levitov**, *"Local rules for quasicrystals,"* **CMP 119 (1988) 627**; **J. E. S. Socolar**, *"Weak matching rules for quasicrystals,"* **CMP 129 (1990) 599**.

> **[INFERRED]** Crucial for the gate: in **every** one of these 3D icosahedral results the forcing lives in **facet decorations / Ammann-plane continuity on ≥2 prototiles** (two rhombohedra, or four ABCK tetrahedra/their octahedra). **None** dissolves the decoration into the *shape of a single connected solid*. The decorations are real matching labels, not yet geometry; the octahedra are *assemblies*, not one prototile. So ABCK is a **strong, perfect-rule 3D quasicrystal on ≥4 (decorated) prototiles** — the *opposite corner* of the design space from the (weak, unmarked, connected) Socolar–Taylor monotile.

---

## 3. HAT & SPECTRE (2D) — and the 3D question

### 3.1 What they are (2D)

- **[CITED]** D. Smith, J. S. Myers, C. S. Kaplan, C. Goodman-Strauss, *"An aperiodic monotile,"* **arXiv:2303.10798** ([abs](https://arxiv.org/abs/2303.10798)), published **Combinatorial Theory, July 2024**. The **hat** is an explicitly **single, connected, simply-connected, UNMARKED polygon (13-gon)** that is **strongly aperiodic** (with reflections). **[CITED]**
- **[CITED]** *"A chiral aperiodic monotile,"* **arXiv:2305.17743** ([pdf](https://arxiv.org/pdf/2305.17743)): the **spectre** — strictly chiral, strongly aperiodic with **rotations + translations only (no reflections)**, connected & unmarked.

These are the gold standard the gate aspires to in 3D: **shape alone, one connected piece, no labels, strong aperiodicity.**

### 3.2 Do the authors address 3D?

**[CITED]** The hat paper **arXiv:2303.10798** is **silent on three dimensions** — it contains **no** mention of 3D / ℝ³ / higher dimensions / SCD (verified by full-text fetch; the paper is entirely 2D). So *within the discovery papers themselves*, a 3D analog is **not claimed and not ruled out** — i.e. **implicitly open**. **[INFERRED]**

The clearest on-record 3D comment from a hat author is **Kaplan 2025**:

> *"Many of the ideas and algorithms we used to prove the hat's aperiodicity could be adapted to work in 3D space, but personally I am daunted by the prospect of deducing the behaviour of any candidate shapes that might be discovered there."* — **C. S. Kaplan, *"The path to aperiodic monotiles,"* arXiv:2509.12216** ([pdf](https://arxiv.org/pdf/2509.12216)), §higher dimensions. **[CITED]** (cross-referenced in [`01_3d_problem_scd.md`](01_3d_problem_scd.md) §1.)

> **[INFERRED]** Reading: the *aperiodicity-proof machinery* (combinatorial hierarchy, "fault lines", computer-assisted substitution) is viewed as **portable** to 3D in principle; the bottleneck is **(a) no candidate 3D shape has been found** and **(b) verifying any candidate's global behaviour is expected to be much harder**. No 3D-hat construction exists as of June 2026. There is a recent group-theoretic recasting — **"Aperiodic monotiles: from geometry to groups," arXiv:2409.15880** ([html](https://arxiv.org/html/2409.15880v2)) — but it does not produce a 3D Euclidean monotile. **[CITED]**

---

## 4. OBSTRUCTIONS / impossibility — what is and isn't proven

### 4.1 Goodman-Strauss: substitution ⇒ matching rules (DECORATED), all d > 1

- **[CITED]** C. Goodman-Strauss, *"Matching rules and substitution tilings,"* **Annals of Mathematics 147 (1998) 181–223** — [Annals](https://annals.math.princeton.edu/articles/12903). **Abstract (verbatim):** *"A substitution tiling is a certain globally defined hierarchical structure in a geometric space; we show that for any substitution tiling in 𝔼ᵈ, d > 1, subject to relatively mild conditions, one can construct local rules that force the desired global structure to emerge."* **[CITED]**
- **Dimensional scope: holds for all d > 1, including d = 3.** The mild conditions are essentially *sibling-edge-to-edge* / non-degeneracy of the substitution. **[CITED]** (abstract); **[INFERRED]** (the named conditions, standard in the literature).
- **Crucial limitation for the gate.** The theorem outputs **matching rules implemented with DECORATIONS/MARKINGS on (generally many) prototiles** — *not* shape-only rules and *not* a single tile. **[INFERRED, strongly supported]** It is a *labels-exist* theorem, agnostic to (a) collapsing labels into geometry and (b) reducing the prototile count to one. So Goodman-Strauss gives, **for free in 3D**, *decorated* matching rules for any nice icosahedral substitution — but says **nothing** about absorbing them into one connected solid.

### 4.2 Is "decoration absorbable into shape?" or "≥2 tiles required" ever proven?

**[CITED+INFERRED]** Search of the literature returns **no general theorem** that decorations can always be absorbed into geometry, **nor** a general lower bound forcing ≥2 prototiles in 3D aperiodic sets. What exists:

- **A concrete unembeddability in a *fixed* dimension** (§1.2): the Socolar–Taylor R2 rule **cannot** sit in a 2D simply-connected disk (it is non-adjacent). This is a *demonstration*, dimension-specific, not a no-go for 3D — and indeed §1.3 shows it *is* absorbable once you add a dimension. **[CITED]**
- **No 2D convex monotile** (a *shape* obstruction, not decoration): every convex polygon tiling the plane also tiles periodically (15 pentagon families, Rao 2017, computer-verified) — [survey arXiv:1508.01864](https://arxiv.org/pdf/1508.01864). **In 3D this obstruction fails**: SCD is a **convex** weakly-aperiodic monotile. **[CITED]** (see [`01_3d_problem_scd.md`](01_3d_problem_scd.md) §4.)
- **Strong vs weak is a real, named gap** (Goodman-Strauss ~2000 convention): *strongly aperiodic* = tilings admit **no infinite cyclic group of Euclidean motions**; *weakly aperiodic* = an infinite cyclic symmetry (e.g. a **screw**) may persist. **[CITED]** ([Einstein problem, Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem); cf. [`04_…`](04_3d_forcing_decidability_group.md) §3.1). Every known 3D monotile (SCD, Socolar–Taylor 3D, variants) is **weak**; **no impossibility theorem** says 3D strong-monotile cannot exist — it is **open**. **[CITED+INFERRED]**

### 4.3 The orientation/chirality and translation-only angles

- **[CITED]** Greenfeld–Tao, *"A counterexample to the periodic tiling conjecture,"* **arXiv:2211.15847** ([abs](https://arxiv.org/abs/2211.15847); [Tao's blog](https://terrytao.wordpress.com/2022/11/29/a-counterexample-to-the-periodic-tiling-conjecture-2/)): a **single finite cluster tiling ℤᵈ by translations only, aperiodically**, in **sufficiently large fixed d** (descends to ℝᵈ). **[CITED]**
- **[CITED]** Greenfeld–Kolountzakis made such a tile **connected** at cost of +2 dimensions ("folded bridges"). (See [`04_…`](04_3d_forcing_decidability_group.md) §4.3.)
- **Limitations for *our* gate.** **[INFERRED]** This is a **different object**: **translations-only**, **very high dimension**, **disconnected by default**, and it has **no Euclidean-isometry / screw content** — so it does **not** address the 3D Euclidean strong-monotile question, and **d = 3 is itself open** (Greenfeld conjectures *no* aperiodic translational monotile in ℤ³). It is the strongest *aperiodicity-from-one-cluster* theorem available, but it buys aperiodicity with **dimension + disconnection + translations-only**, exactly the resources the 3D Euclidean problem forbids.

---

## STATE OF THE ART — summary table

| Example | #prototiles | Marked? (shape-only?) | Connected? | Aperiodicity flavor | Forces substitution exactly? | Citation |
|---|---|---|---|---|---|---|
| **Socolar–Taylor 2D, color version** | 1 | **Marked** (2 color rules R1,R2) | connected hexagon | strong (2D) | — (forces ST hierarchy) | [arXiv:1009.1419](https://arxiv.org/abs/1009.1419) **[CITED]** |
| **Socolar–Taylor 2D, shape-only** | 1 (declared) | shape-only | **DISCONNECTED** (islands / cutpoints) | strong (2D) | — | [arXiv:1009.1419](https://arxiv.org/abs/1009.1419) **[CITED]** |
| **Socolar–Taylor 3D** | **1** | **shape-only (NO color)** | **connected, simply-connected** | **WEAK** (periodic stacking) | — | [arXiv:1009.1419](https://arxiv.org/abs/1009.1419) **[CITED]** |
| **Schmitt–Conway–Danzer (SCD)** | 1 | unmarked | connected, **convex** biprism | **WEAK** (screw axis) | n/a (not a model set; singular diffraction) | [Einstein prob., Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem); [Baake–Frettlöh math-ph/0411052](https://arxiv.org/abs/math-ph/0411052) **[CITED]** |
| **Danzer ABCK (octahedra)** | **4** tetrahedra (→ octahedra) | **marked** (perfect local/packing rules; Ammann-plane) | each tetra connected; octahedra are *assemblies* | **strong**, icosahedral quasicrystal | **YES — perfect rules force the substitution exactly** | [Danzer 1989](https://www.sciencedirect.com/science/article/pii/0012365X89902823); [Frettlöh–Baake ikosa](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf) **[CITED]** |
| **Ammann rhombohedra (3D Penrose)** | **2** | **marked** (facet decorations) | connected rhombohedra | strong, icosahedral | **YES (Katz, no self-similarity used)** | [Katz 1988, Project Euclid](https://projecteuclid.org/euclid.cmp/1104161989) **[CITED]** |
| **Hat (2D)** | 1 | **unmarked** | connected simply-conn. 13-gon | **strong** (w/ reflections) | n/a (combinatorial hierarchy) | [arXiv:2303.10798](https://arxiv.org/abs/2303.10798) **[CITED]** |
| **Spectre (2D)** | 1 | unmarked | connected | **strong, chiral** (rot+transl only) | n/a | [arXiv:2305.17743](https://arxiv.org/pdf/2305.17743) **[CITED]** |
| **Greenfeld–Tao cluster** | 1 | unmarked | disconnected (connectable +2 dim) | aperiodic **translations-only**, high d | n/a | [arXiv:2211.15847](https://arxiv.org/abs/2211.15847) **[CITED]** |
| **Goodman-Strauss (any nice substitution, d>1)** | many | **marked (decorations)** | per-prototile | matches the substitution | **YES (forces it)** | [Annals 147 (1998)](https://annals.math.princeton.edu/articles/12903) **[CITED]** |
| **3D strongly-aperiodic single tile** | **1?** | ? | ? | **strong** | — | **OPEN — no construction, no impossibility** **[INFERRED]** |

---

## OBSTRUCTION ASSESSMENT

**How hard is the single-geometric-tile collapse of octahedral matching rules, and what is provably impossible?**

From the sources, three facts frame the answer. **(1) The collapse is *demonstrably possible in the weak regime, and only there so far.*** Socolar–Taylor **prove by construction** that a genuine matching rule — even one that is *provably* non-embeddable in a connected disk in its native dimension because it couples non-adjacent tiles — can be **fully absorbed into the shape of one simply-connected, unmarked 3D solid** *("enforced by the shape of the tile alone")* **[CITED, arXiv:1009.1419]**. So "geometric realizability on a single connected tile" is **not** the obstruction; the obstruction is **strength**: that same construction spends the third dimension routing the long-range channel and is left with a **periodically-stacked slab → weakly aperiodic**. **(2) The strong, perfect-rule 3D quasicrystals we know (ABCK octahedra; Ammann rhombohedra, Katz) keep their force in *decorations on ≥2 prototiles*** — ABCK on **four** tetrahedra (octahedra are assemblies, not a prototile), Penrose on **two** rhombohedra; **[CITED, Danzer 1989 / Katz 1988]**. No source dissolves those decorations into one connected solid, and Goodman-Strauss's theorem (which *does* give decorated rules for any nice substitution in all d > 1, **[CITED, Annals 1998]**) is explicitly a *labels-exist*, *many-tiles* result — it neither absorbs labels into geometry nor reduces the count to one. **(3) Nothing in the literature is *proven impossible* on the target.** There is **no theorem** forbidding a strongly aperiodic single (even unmarked) 3D Euclidean tile, **no** lower bound forcing ≥2 prototiles in 3D, and **no** general no-go on absorbing decorations into shape; the only hard *impossibility* in the area is the **2D convex** obstruction, which **already fails in 3D** (SCD). The translation-only Greenfeld–Tao monotile is the strongest one-tile aperiodicity theorem but lives in **high dimension, disconnected, translations-only**, with **d = 3 open** — it does not touch the Euclidean-isometry strong-monotile question. **Net assessment [INFERRED from the above CITED facts]:** the *gate-passing event* the program needs (octahedral/decoration matching rules collapsed onto **one connected solid**) is **realized for weak aperiodicity** and **unobstructed-but-unconstructed for strong aperiodicity**. The barrier is the **screw/stacking residue** common to SCD and Socolar–Taylor — killing the last infinite-cyclic symmetry while keeping one connected prototile — and the consensus difficulty (Kaplan 2025, **[CITED]**) is **search + verification**, *not* a proven wall. For this track that means the 3D strong-monotile point is a **door, not a wall**: the precise thing to construct is a single connected solid whose shape forces the ABCK-type icosahedral (genuinely 3D, screw-free) hierarchy — equivalently, **dissolve the Katz/Danzer facet decorations into geometry without re-introducing a periodic axis.**

---

## Source ledger (primary, with URLs)

- Socolar–Taylor, *Forcing nonperiodicity with a single tile*, Math. Intelligencer 34 (2012) — [arXiv:1009.1419](https://arxiv.org/abs/1009.1419) / [ar5iv](https://ar5iv.labs.arxiv.org/abs/1009.1419)
- Socolar–Taylor, *An aperiodic hexagonal tile*, JCTA 118 (2011) — [arXiv:1003.4279](https://arxiv.org/abs/1003.4279)
- Socolar–Taylor tile — [Wikipedia](https://en.wikipedia.org/wiki/Socolar%E2%80%93Taylor_tile)
- Danzer, *Three-dimensional analogs of the planar Penrose tilings and quasicrystals*, Discrete Math. 76 (1989) 1–7 — [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0012365X89902823)
- Frettlöh–Baake, *Icosahedral tilings in ℝ³: the ABCK tilings* — [Bielefeld PDF](https://www.math.uni-bielefeld.de/~frettloe/papers/ikosa.pdf)
- Koca et al., *Icosahedral polyhedra from D6 lattice and Danzer's ABCK tiling*, Symmetry 12 (2020) 1983 — [MDPI](https://www.mdpi.com/2073-8994/12/12/1983) (HTTP 403 in-tool; metadata via search)
- Zerhusen, *Danzer's ABCK tiling* exposition — [ms.uky.edu](https://www.ms.uky.edu/~lee/zerhusen/quasi.html)
- Baake–Grimm, *Aperiodic Order Vol. 1*, CUP 2013 — [Cambridge](https://www.cambridge.org/core/books/abs/aperiodic-order/more-inflation-tilings/1D706353EF4545718A3792A2102677AB)
- Katz, *Theory of matching rules for the 3-dimensional Penrose tilings*, CMP 118 (1988) 263–288 — [Project Euclid](https://projecteuclid.org/euclid.cmp/1104161989) / [Springer](https://link.springer.com/article/10.1007/BF01218580)
- Smith–Myers–Kaplan–Goodman-Strauss, *An aperiodic monotile* — [arXiv:2303.10798](https://arxiv.org/abs/2303.10798)
- *A chiral aperiodic monotile* (spectre) — [arXiv:2305.17743](https://arxiv.org/pdf/2305.17743)
- Kaplan, *The path to aperiodic monotiles* — [arXiv:2509.12216](https://arxiv.org/pdf/2509.12216)
- Goodman-Strauss, *Matching rules and substitution tilings*, Annals 147 (1998) 181–223 — [Annals](https://annals.math.princeton.edu/articles/12903)
- Greenfeld–Tao, *A counterexample to the periodic tiling conjecture* — [arXiv:2211.15847](https://arxiv.org/abs/2211.15847) / [Tao blog](https://terrytao.wordpress.com/2022/11/29/a-counterexample-to-the-periodic-tiling-conjecture-2/)
- Baake–Frettlöh, *SCD patterns have singular diffraction* — [arXiv:math-ph/0411052](https://arxiv.org/abs/math-ph/0411052)
- Einstein problem — [Wikipedia](https://en.wikipedia.org/wiki/Einstein_problem)

### In-tool fetch caveats (transparency)
- arXiv `*.pdf` endpoints (1003.4279, 2003.13449, 1205.3633, ikosa.pdf, einstein.pdf) returned **binary that did not render to text** in-tool; readable content came from the **ar5iv HTML mirror** (for 1009.1419 — the load-bearing Socolar–Taylor quotes are from this clean fetch) and from **search-index excerpts** (for the ABCK "perfect rules" verbatim string and the Kaplan/hat 3D-silence checks, the latter confirmed by a full-text fetch of einstein.pdf reporting no 3D mention).
- MDPI and ResearchGate pages returned **HTTP 403**; those facts are corroborated from the Bielefeld/Kentucky sources and search excerpts.
- The **one item I could not pin to a single clean citation** is the *standalone proof attribution* for "ABCK perfect rules on octahedra" — it is Danzer's program (1989 / Danzer–Papadopolos–Talis 1993) as exposited in Frettlöh–Baake / *Aperiodic Order* Vol. 1, resting on Katz-1988-style Ammann-plane technology, but a dedicated "Theorem: ABCK rules are perfect" paper was not isolated in-tool. Flagged **[INFERRED]** above; the Bielefeld ikosa PDF or *Aperiodic Order* §5–6 closes this.
