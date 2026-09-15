# Focused 3D synthesis — a strongly-aperiodic 3D monotile via the shadow method

Target (chosen 2026-06): a **strongly-aperiodic 3D monotile** ("the 3D einstein"), via the
shadow/strict-extension method ([../../docs/APPROACH.md](../../docs/APPROACH.md)). Four focused, cited
pillars below; this synthesis turns them into one concrete plan and the first cascade move.

## The four pillars

| # | Doc | Core |
|---|-----|------|
| 01 | [01_3d_problem_scd](01_3d_problem_scd.md) | The target & SCD; **strong = trivial stabilizer (no screw)**; SCD is a *degenerate* shadow (circle internal space → singular-continuous) |
| 02 | [02_3d_quasicrystals_superspace](02_3d_quasicrystals_superspace.md) | The higher layer: **ℤ⁶/D₆ → ℝ³**, triacontahedron window, τ³; **D₆ Coxeter polynomial factors into expanding-τ / contracting-σ blocks** |
| 03 | [03_3d_substitution_inflation](03_3d_substitution_inflation.md) | Danzer ABCK & 3D Penrose = **τ³ Pisot model sets**; recognizability proven in ℝᵈ; **non-golden cubic Pisot = best unrealized target** |
| 04 | [04_3d_forcing_decidability_group](04_3d_forcing_decidability_group.md) | Katz/Socolar matching rules force the icosahedral QC (decidable, Le's island); Greenfeld–Tao = method + warning; rarity trident transfers |

## The convergent picture (one coherent plan)

The four pillars agree, and together they say our method is **unusually well-matched to this open problem**:

1. **Target & certificate (01, 04).** A strongly-aperiodic 3D monotile is **open (2026)**; "strongly aperiodic"
   sharpens to **trivial stabilizer of every lift — no surviving infinite-cyclic / screw symmetry.** This is
   *exactly* the gap by which SCD and the connected Socolar–Taylor tile fail. Our strict-extension certificate
   (δ_fact ≠ ∅, pure-point) is precisely "no screw."
2. **The higher layer is already built and pure-point-*proven* (02, 03).** The periodic upstairs is
   **ℤ⁶/D₆ → ℝ³** with the **rhombic-triacontahedron window**; inflation **τ³ = 2+√5**. Danzer ABCK and the
   2-tile golden rhombohedra are τ³ **model sets**. We are not constructing the higher layer from scratch — it
   exists.
3. **The eigenvalue audit (T1) is literally a polynomial factorization (02).** The **D₆ Coxeter polynomial
   factors into an expanding τ-block (physical) and a contracting σ-block (internal)**, σ = −1/τ. The
   non-descending object is the τ-expansion; the audited descent is the σ-contraction; the audit *is* this
   split. (Danzer charpoly x⁴−5x³+2x²+5x+1; 3D-Penrose x²−4x−1.)
4. **Recognizability (our certificate) provably holds in 3D (03).** Solomyak: unique-composition ⇔
   aperiodicity in ℝᵈ for all d; Lee: substitution ⇔ regular Euclidean model set (unimodular, pure-point);
   the 3D Rauzy analogue is the (fractal) atomic surface.
5. **Forcing is proven and decidable on our island (04).** Finite matching rules already force the 3D
   icosahedral quasicrystal (Katz 1988, Socolar 1990) because the ℤ⁶→ℝ³ slope is algebraic — inside **Le's
   enforceable locus**. The rarity trident (Le measure-zero + Hochman–Meyerovitch + Berger) transfers, capped
   by Greenfeld–Tao monotile-undecidability.
6. **The structural advantage over SCD (01, 02).** A *model-set* monotile is **strongly aperiodic for free —
   no screw** (Euclidean internal space → pure-point). SCD leaks a screw precisely because its upstairs is
   degenerate (circle internal space). Our route avoids the SCD trap by construction.

## The two design axes (the open doors — Mode B)

Everything above is **built or proven**. The genuine open content is the *design*, on two axes:

- **Axis A — single-prototile collapse (the hat analogue).** A **3D fractal-window reprojection** collapsing a
  τ³ protoset (2 golden rhombohedra, or 4 ABCK tetrahedra) to **ONE** prototile — the direct 3D analogue of
  how the hat's fractal Rauzy window collapses the planar protoset (Baake–Gähler–Mazáč 2024–25). **Open.**
  *(An unrefereed 2025 Taillefer preprint informally targets triacontahedron + "fractal antennas" — a lead,
  not a result; it lacks the CPS/recognizability/gap-labeling rigor our method supplies.)*
- **Axis B — a new (non-golden) Pisot inflation.** Every strongly-ordered 3D inflation on record uses a power
  of τ; a **non-golden cubic Pisot** (plastic number ρ ≈ 1.3247, or another cubic unit) is the best
  *unrealized* inflation — and even its 3D *realizability* is open (the ℝ³ Perron converse is unproven). A new
  Pisot ⇒ a new aperiodicity class.
- **The combined prize:** a **single-tile, non-golden-Pisot, screw-free 3D model set** — strongly aperiodic by
  construction, with a Lean/finite-checkable certificate.

## The concrete cascade plan

- **Mode A (earn its place).** Re-derive a *known* strongly-ordered 3D structure through our certificate: take
  Katz's icosahedral matching rules + the Danzer/rhombohedra τ³ model set and show the certificate fires —
  pure-point (Coxeter-factorization audit), recognizability (δ_fact ≠ ∅), trivial stabilizer (no screw),
  AP-inverse-limit hull. *(These are protoSETS of 2–4 tiles, not monotiles — that is the gap Mode B closes.)*
- **Mode C (recombine).** Recombine the validated SAU profiles (InvDesc/AggInv eigenvalue audit + ObsLed
  no-screw obstruction) for the monotile target.
- **Mode B (design from the descent expression).** Axes A and B above, ideally combined. This is where a new
  tile is born; invoke assertively once A/C clear smuggling.

## PROVEN vs OPEN (the map)

| Item | Status |
|------|--------|
| Strongly-aperiodic 3D monotile exists | **OPEN** (Kaplan arXiv:2509.12216) |
| SCD = convex weakly-aperiodic 3D monotile | PROVEN (only weak; screw) |
| ℤ⁶/D₆ → ℝ³ icosahedral model set, τ³, triacontahedron window | PROVEN |
| Danzer ABCK & 3D Penrose are τ³ Pisot model sets | PROVEN |
| Recognizability ⇔ aperiodicity in ℝᵈ (all d) | PROVEN (Solomyak) |
| Matching rules force 3D icosahedral QC (Le's island) | PROVEN (Katz, Socolar) |
| ℝ³ Perron *converse* (which Pisot expansions are realizable) | **OPEN** |
| Single-prototile fractal-window collapse in 3D | **OPEN** (our Axis A) |
| Non-golden cubic Pisot 3D inflation realized | **OPEN** (our Axis B) |

## Honesty (overclaim guard)

The certificate (recognizability) and the audit machinery (Coxeter factorization, AP inverse limit,
gap-labeling) are **established mathematics** — re-expressions, not new theorems. **Our genuine contribution
is (i) the agentic theory-space walk, (ii) the *design* on Axes A/B, and (iii) an actually-new tile** — not the
topology. The Taillefer preprint is unverified. "Most eyebrows" = hardest = lowest odds; the realistic partial
wins (a new 3D substitution / a new occupation-domain structure / a screw-free protoset reduction) are
themselves results.

## First move (the first cascade dispatch, when kicked off)

**Mode A, step 1:** instantiate the closure package for the **ℤ⁶/D₆ → ℝ³ icosahedral model set with τ³
inflation**, and run the certificate on it — verify pure-point via the Coxeter-polynomial factorization
(the T1 audit), recognizability (δ_fact ≠ ∅), and trivial stabilizer (no screw). This *earns the method's
place* on known-good ground before Mode B attempts the single-tile / new-Pisot collapse. Parked pending go.
