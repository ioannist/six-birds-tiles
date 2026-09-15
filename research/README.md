# Research dossier — aperiodic monotiles as audited shadows of higher layers

Seven independently-researched, fully-cited pillars (online research, 2026-06), plus this synthesis.
Read [../docs/APPROACH.md](../docs/APPROACH.md) first for the strategy these support.

## The seven pillars

| # | Doc | What it covers |
|---|-----|----------------|
| 01 | [einstein_problem_and_monotiles](01_einstein_problem_and_monotiles.md) | Wang→Penrose→Socolar–Taylor→hat/spectre; the Tile(a,b) continuum; the two aperiodicity proofs; discovery story; open problems |
| 02 | [cut_and_project_model_sets](02_cut_and_project_model_sets.md) | **The shadow formalism**: lattice+window+irrational slope, model/Meyer sets, star map, pure-point diffraction; hat = fractal-window reprojection |
| 03 | [substitution_inflation_pisot](03_substitution_inflation_pisot.md) | Inflation factors, Perron–Frobenius, **Pisot/Salem admissibility**, the Pisot conjecture, **recognizability = our certificate**, the projection↔substitution duality |
| 04 | [quasicrystals_superspace](04_quasicrystals_superspace.md) | **The physics instance**: Shechtman, superspace crystallography (higher-dim periodic → shadow), phasons, diffraction, real materials |
| 05 | [tiling_spaces_cohomology_hull](05_tiling_spaces_cohomology_hull.md) | The hull as **inverse limit** (Anderson–Putnam) = our T2; PE/Čech cohomology, **gap-labeling** = our T1 |
| 06 | [matching_rules_SFT_decidability](06_matching_rules_SFT_decidability.md) | Wang/undecidability; **local-rules↔projection** (Le, Bédaride–Fernique); substitution→rules (Goodman-Strauss); **the rarity engine** |
| 07 | [frontiers_methods_outofdiscipline](07_frontiers_methods_outofdiscipline.md) | Discovery software/SAT; **the open frontiers** (hyperbolic/3D); inflation = RG fixed point; tiling catalogues |

## What the research established

### 1. Our picture is mainstream mathematics — with exact theorems
"Aperiodic tiling = down-shadow of a higher periodic layer" is literally the **cut-and-project / model-set**
construction (02), and its mature physical instance is **superspace crystallography** (04): a quasicrystal
is a genuinely periodic structure in higher-dimensional space recovered by an irrational cut. The
**projection chart and the substitution chart are dual**, glued by a **Pisot** number (03): the contracting
internal-space window is the **Rauzy fractal** living in the Galois-conjugate space.

### 2. Our certificate already has a name: *recognizability*
The strict-extension / non-factorization certificate (`π₁` doesn't factor through `π₀`) is exactly
**recognizability / unique composition** (03, 06): Mossé (aperiodic primitive ⇒ recognizable with a finite
window) and Solomyak (unique composition ⇔ aperiodicity). In symbolic-dynamics terms it is the
**sofic-but-not-SFT gap** (06): the local layer (π₀, an SFT) under-determines the global hierarchy (π₁),
and the fiber-collision-with-split *is* that gap. This is a faithful re-description, not a new theorem —
see the honesty caveat below.

### 3. The two "to-build" theorems are mostly *existing topology* (de-risk + caveat)
- **T2 (stacking-composition) ≈ Anderson–Putnam.** A substitution tiling space *is* the inverse limit of one
  branched manifold (the AP complex) under the inflation self-map (05) — a citable theorem (Anderson–Putnam
  1998; Sadun–Williams 2003) = our tower / F43. T2 = composition of the inverse-limit bonding maps;
  collaring ⇒ border-forcing ⇒ recognizability is the proof skeleton.
- **T1 (spectral drive) ≈ gap-labeling.** The `∮_γ a` audit is the PE/Čech pairing; the drive is the Perron
  eigenvalue; the trace-budget is the contracting Galois conjugates; **Bellissard gap-labeling** certifies the
  eigenvalue as a finite K-theory-valued topological invariant (the patch-frequency ℤ-module) (05).

### 4. The rarity / forcing argument has three real ingredients (06)
"Almost no local rule admits a consistent hierarchical lift" is supported by: **Le's obstruction** (any slope
admitting local rules is *algebraic* → a measure-zero locus of slopes), **Hochman–Meyerovitch** (ℤᵈ-SFT
locally-admissible counts converge to entropy *from above* → the quantitative SFT⊊sofic gap), and **Berger
undecidability** (no algorithm decides tileability in general). This is the tiling form of Foundations I's
Finite Forcing Lemma we owed.

### 5. Strategic reframe — the planar Euclidean *existence* question is closed; classification is open (07)
The hat + spectre **settled the existence question** (an aperiodic monotile *exists*); the general inverse
problem is **undecidable** (Berger; Greenfeld–Tao 2025). But there is **no classification theorem** — an
*essentially-different* planar monotile (a new Pisot inflation / symmetry class) is **not ruled out** and would
be a genuine result. What *is* impossible in the Euclidean plane is a **convex** aperiodic monotile (every
convex polygon that tiles also tiles periodically) — which is exactly why the *hyperbolic convex* case is open.
**(Correction:** an earlier draft of this synthesis said "the planar monotile is closed" — only *existence* is
closed.) The highest-impact open frontiers:
- **Hyperbolic plane** — a strongly aperiodic *convex* monotile is reported open (07 cites Maiti
  arXiv:2603.27827 — *verify*). Highest-value, best-defined target.
- **3D / higher dimensions** — strongly-aperiodic (Schmitt–Conway–Danzer is only *weakly* aperiodic).
- **A new Pisot / symmetry class** — a planar tiling with an inflation factor / symmetry not yet realized as a
  single-prototile shadow.

### 6. The design handle — how to actually hunt
A new monotile ≈ **a new (Pisot inflation λ, window W) pair in a low-dimensional cut-and-project scheme**
(02, 03). The hat is the proof of concept: it is a reprojection of a regular model set whose **fractal Rauzy
window is exactly what collapses the protoset to a single tile** (02; Baake–Gähler–Mazáč–Sadun arXiv:2411.15503,
Baake–Gähler–Mazáč–Mitchell arXiv:2502.03268). Realizability tests we now have:
- **Admissibility of λ:** must be **Perron** (Thurston/Kenyon, necessary & sufficient in the plane) and
  **Pisot/Salem** for pure-point order (03).
- **Local-rule realizability of a slope:** **Le's algebraicity** obstruction and the **Bédaride–Fernique
  decidable coincidence/Plücker** criterion (06).
- **Substitution → matching rules:** Goodman-Strauss (every substitution tiling is enforced by finite rules) (06).
- **Practical pattern:** heuristic *walk* + exact *verifier* (07), over the enumerable knowledge base of
  already-realized shadows (Tilings Encyclopedia; Gähler–Kwan–Maloney generator).

## Map to our certificate and theorems

| Our object ([../docs/CERTIFICATE.md](../docs/CERTIFICATE.md)) | Established machinery it rests on |
|---|---|
| Higher layer / non-descending object | CPS lattice `L` + irrational slope / Pisot λ (02, 03, 04) |
| Audited descent (the shadow) | the projection `π`; descent-legality = regular-model-set ⇒ pure-point (02) |
| Strictness `δ_fact≠∅` | recognizability / sofic-not-SFT gap (03, 06) |
| Eigenvalue audit (T1) | Perron factor + gap-labeling K-theory invariant (03, 05) |
| Stacking / hull (T2) | Anderson–Putnam inverse limit (05) |
| Saturation (no period) | irrational slope ⇒ no period; Le measure-zero (02, 06) |
| Rarity | Le + Hochman–Meyerovitch + Berger (06) |

## Honest caveats (per the overclaim guard)
- **Relabeling risk is concrete.** Items 2 and 3 show our certificate (recognizability) and our two theorems
  (Anderson–Putnam, gap-labeling) are largely **re-expressions of established results**. SBT's genuine
  contribution is therefore **(a) the agentic theory-space walk, (b) the *design* of a new (λ, W) shadow, and
  (c) an actually-new tile** — *not* the certificate framing or re-deriving the topology. Keep this front-and-center.
- **Verify the hyperbolic-frontier citation** (arXiv:2603.27827) before relying on it.
- The hat's CPS description (fractal window) is recent (2024–25) and technical; treat it as a lead to study,
  not a settled tool.

## Next move (informed)
The first step *upstairs* is now concrete: **pick the open setting (recommended: hyperbolic, or a new planar
Pisot class) and a candidate (λ, W) shadow, earn the move's place by re-deriving a known one (hat = fractal
Rauzy window; Ammann–Beenker = silver ratio), then walk to an unrealized (λ, W).** This is the first Mode-A→B
dispatch of the cascade — still parked pending go.
