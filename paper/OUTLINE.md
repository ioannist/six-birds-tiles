# OUTLINE.md — the R44 paper, paragraph by paragraph (v2, 2026-09-08)

WRITING_PLAN.md step 9. Each bullet is one paragraph (or one displayed statement), tagged with its
ledger rows (`CLAIMS_LEDGER.md` ids), its borrowed-language source (paper and line, per
`COMMUNITY_PAPER_PROFILE.md` and `PAPER_PLAN.md` §4), its figures/tables (`FIGURES.md`), and a word
budget. Section numbers follow `PAPER_PLAN.md` §3 (1:1 with THEOREM.md at the pinned state,
DECISIONS.md Q-F). Total budget ≈ 15,000 words of body text plus appendices. Venue: Combinatorial
Theory.

Owner rulings encoded here (WRITING_PLAN.md §0): the way the tile was found is the organizing idea of
the exposition; Six Birds language appears in §3.3 only; everywhere else the same ideas are in the
audience's language; the private thread is never a source; every claim keeps its tier; the
"proof submission" qualifier appears in the abstract and the front matter.

Title: **A strongly aperiodic monotile in three dimensions** (PAPER_PLAN.md §2).

## Abstract (the one piece of Phase-1 prose; ≈ 190 words; hat abstract L13 as the form)

> Socolar and Taylor asked for a single, simply connected three-dimensional prototile that forces
> nonperiodicity by shape alone, admitting no weakly nonperiodic tiling; the Schmitt–Conway–Danzer
> biprism and the three-dimensional Socolar–Taylor tile admit screw motions or a periodic stacking
> direction. We exhibit a rational polyhedral 3-ball Q, a seven-cube chair whose 24 exposed unit
> panels carry tiny square-pyramid features, and prove, as a proof submission, that Q admits tilings
> of R³ by congruent copies, reflections allowed, and that every such tiling has no translational
> period and a symmetry group of order at most 24; every tiling is homochiral and carries a unique
> infinite hierarchy of nested supertiles. The solid was designed to a reading of the
> aperiodic-monotile phenomenon reached with the Six Birds emergence calculus (Section 3.3), and
> the construction turns on a single finite test, checked by machine: the tile's own contact rule
> survives coarsening, so that the decoded parent tiling obeys the tile's rule and no other. The
> proof combines a written geometric argument, that the features force
> every tiling onto a registered lattice, with exhaustive finite enumerations; the companion census is
> replayed by two independent implementations, every finite gate is kernel-checked in Lean 4 (modulo a
> named compiler hook per `native_decide` theorem), and the logical assembly from the remaining
> written lemmas to the theorem is itself a Lean theorem over those lemmas, listed by name.

Ledger: Q1, Q6, Q7, T1–T4, T6, T8, O1, O4, H5, M1–M3, D4 (qualifier: "as a proof submission" and the
front-matter sentence), Q23 (no "longstanding"/"open" claim), H6 and the Q-G authors' account for the
provenance sentence (the framework is named, not used; owner instruction 2026-09-09). No Six Birds vocabulary (T-j).

## 1 Introduction (≈ 3,100 words)

### 1.1 The einstein problem in R³ (≈ 1,100)
- Opening: the two quotations verbatim (Q1, Q2); then "The solid Q of Figure 1.1 is such a
  prototile." Fig 1.1. [2303.10798 L13 form; Q23: attribute the problem to its authors, no
  "longstanding open" wording]
- Wang, Berger, Robinson, Penrose, Jeandel–Rao in the hat's order (Q21). [2303.10798 L18–L24]
- The near-misses and what each concedes: Gummelt, Penrose 1+ε+ε², Taylor–Socolar,
  Walton–Whittaker, Mampusti–Whittaker (Q12), Greenfeld–Tao (Q8). [2303.10798 L26–L35]
- The hat and the Spectre settle the plane (Q9, Q10); simplified proofs and the structural
  literature, one sentence (BGS25, BGMM25, Soc23, AA25).
- Three dimensions: Hilbert's 18th problem and Reinhardt; the SCD biprism (Q7); Socolar–Taylor's 3D
  tile (Q6); Fletcher's cubic prototile with an atlas rule (Q13); Kaplan's "cautionary tale" (Q2).
  Weak vs strong aperiodicity: in the plane they coincide (Q4); in R³ they do not; Mozes's notion (Q3);
  the finer taxonomy of Coulbois et al. and the mild/strong caveat (Q5, T5).
- What Q is not: not convex (O10; SCD is), not simple; what it is: a closed 3-ball with rational
  coordinates and no matching rules (O1, O4, N4).

### 1.2 Main result (≈ 500)
- Theorem 1.1 and Theorem 1.2 as in STATEMENT.md §2; "In this paper we prove the following"
  [2303.10798 L42]; what is and is not assumed (T10, T11): local finiteness is proved, not automatic
  [2303.10798 L58]. Front-matter sentence: the proof-submission qualifier and where the remaining
  written lemmas are listed (D4, T12).
- Homochirality and the Spectre's definition (T6, T7, D5); reflections allowed but never mixed
  [2305.17743 L22; 1009.1419 L72]. The congruence-convention paragraph (D7) [2303.10798 L52–L54].

### 1.3 What an aperiodic monotile is, and how that found Q (≈ 1,000; audience's language only)
- Periodicity as factoring: a lattice labelling is p-periodic exactly when it factors through
  Z³/⟨p⟩ (elementary). For tilings of Q the paper states only the direction the proof provides:
  every tiling admits a registration (`registration_of_tiling`, T3-backed), and under registration
  and native asymmetry (T3-backed through the carrier-recovery field, with the T1n frame reduction
  and the T1 48-frame comparison; O5) every period is an integer vector
  (`period_grid_from_registered_poses`); no packaged equivalence with a label encoding is claimed. A monotile is an einstein when legal
  tilings exist but none is periodic; the local pieces do globalize, what fails is globalizing
  them periodically (H1). [elementary; bridge by the named declarations at their tiers]
- The hierarchy must be forced, not drawn: a grouping certifies aperiodicity only if the tiling
  determines it and every symmetry preserves it (stabilizers pass to every extracted level); this is
  recognizability, unique composition and period halving (H3). [1608.07165 L80, L308; 2305.17743 L43]
- What one shape adds: the matching rule moves into what can physically fit; three requirements for
  a marked system to become a bare solid, the third being the one that is easy to lose: the bare
  solid must not admit an extra periodic tiling (H4). One shape, many roles.
- The design test this yields, and its finite form: the halving argument needs the decoded parent
  language to lie inside the fine language; equality is the sufficient form checked for Q, the
  halved parent atlas equals the fine atlas (H5, `parent_atlas_eq_fine`); sufficient, not necessary.
- One pointer sentence: the reading was reached with an emergence framework, discussed in §3.3, where
  its statement of the phenomenon is quoted and related, clause by clause and at each clause's tier,
  to the theorems proved here (H2, H6, H11).
- The proof as the discharge of that reading: existence (§3), every tiling decodes (§4–§5), unique
  parent and hierarchy (§6), the scale that breaks p is period halving (§7); the census carries only
  universality, not existence [2303.10798 L51] (H11, N7). Roadmap Fig 1.2.

### 1.4 Computer assistance and verification (≈ 400)
- The disclosure paragraph: what was enumerated (Table 2), the companion census by two independent
  implementations (M3, not "every enumeration"), every finite gate kernel-checked with the
  `native_decide` hook named per theorem (M1, M2), the spine over the named remaining lemmas and the
  count at the pinned state (T12), exact arithmetic (M4), controls (M5), "Code." pointer (M7), the
  Myers comparator (Q20). [2303.10798 L51, L158; 1808.07768 L51, L253; 1506.06492 L94]

### 1.5 Terminology (≈ 350)
- The definitions block of STATEMENT.md §3 with sources (D1–D5); the disambiguation sentence (T5);
  monotile/einstein restated for closed 3-balls (D2); registered/atlas/supertile (D3).

## 2 The solid Q (≈ 1,000)
- The chair carrier P, the 24 panels, the 8 features per panel, heights ±j/10000, base half-width
  1/100, rational coordinates, volume 7 (O1, O9); Figs 2.1–2.3.
- The profile: 30-state closure, 372 sign equations, 12 balanced components (R1).
- Mesh facts and the 3-ball (O2–O4; Table 5); the two classical imports stated exactly.
- No self-isometry with its component tiers (O5, R12); the 192 roles and the 24 distinct
  deviations (O6, O7); the tube construction (A16).
- The parameter family (T14) as the hat states Tile(a,b) [2303.10798 L80, Thm 6.1].

## 3 Finding Q (≈ 1,900)
### 3.1 The substitution (≈ 500)
- Eight child poses partition 2P (O8); Fig 3.1; supertiles Fig 3.2; the 44-contact atlas and the
  24 frames (R2, R3); Fig 3.3 / Table 2. The viewer sentence (Q22) [2303.10798 L96].
### 3.2 The design test in finite form (≈ 300)
- The halved parent atlas equals the fine atlas; the 19 contact frames generate the full proper
  cubic group (H5, R3, R7); why this is what makes period halving legitimate (R§8, R§10).
### 3.3 How the tile was found (≈ 800; the ONE section with Six Birds language, per DISCOVERY.md)
- Labelling sentence: "This section records how the solid was found; nothing in it is used in the
  proofs." The three steps first, with their numbers and packets: the marked chair with its finite
  evidence and its honest gap (H7); the first bare solid as a periodic control, 62 → 398 (H8); the
  frame change, 44 = 44 with the 24-element frame group (H9). Provenance sentence (hash chain).
- Then the reading that produced the steps, as the authors' account corroborated by the packets'
  compass statements (H4, H6): the framework named once with citations; Theorem G11 quoted with its
  two hypotheses and its calibration list; the role reading; the instantiation for the registered
  system C_44, clause by clause with tiers, carried to Q by registration and realization; the tower
  in place of per-period certificates (H2, H11); the gates F7/F28 as the packets' structural
  interpretation (H5).
- What the method did not do (H10); the framework's own wording discipline (H6): it supplied a
  reading and a test; every claim is certified by the proof and the verification record.
### 3.4 Existence (≈ 300)
- The registered baseline tiling and the small-collar realization (R10, E2, E6) [2305.17743 L35
  "There exists a Spectre" pattern]: a tiling exists (T1).

## 4 Features force companions (≈ 2,200; A§2–4)
- Local finiteness (A1); sector budgets (A2); the complete dihedral list and the distinct deviations
  (A3, O6); generic feature-edge partner (A4); Fig 4.1; errata E1, E3 (A17).
- The circular cone at L = 3/25 and the containment (A5, A6).
- Theorem 4.2: one tile accompanies the whole feature graph (A7); rigidity (A8); the companion pose
  is discrete (A9). [1003.4279 L28 register]

## 5 Every tiling is registered (≈ 1,800; A§5–6, R§5)
- Baseline overlap ⇒ core overlap (A10); the census 6,862 → 5,317 → 44 with 299,975 boxes (A11;
  Table 2; Fig 4.2; Appendix B); only registered mates (A12).
- Component covers the grid (A13) and the solids cover R³ (A14); erratum E6.
- Theorem 6.3, unrestricted alignment (A15); the "preserves periodicity" sentence [2305.17743 L53].

## 6 The unique hierarchy (≈ 1,600; R§7–9)
- 33 first shells, 14/18 completions, 28 conflicts, Theorem 7.1 (R4–R6); Fig 6.1; Table 2.
- Coarsening: 697 → 116 → 44, all even, halved = fine atlas, admissibility, common parity, the halved
  baseline tiling (R7, E4).
- The intrinsic hierarchy theorem (T8) and its uniqueness; no exhaustion clause and the fault-line
  sentence (T9, N1) [2303.10798 L253]; local derivability not claimed (N2); Fig 6.2; nested controls
  (R8).

## 7 Aperiodicity and homochirality (≈ 900; R§10)
- Period halving p/2ⁿ ∈ Z³ ⇒ p = 0 (T13, T2); the 24-frame injection and |Sym(T)| ≤ 24 (T3); hence
  no infinite-order symmetry: strongly aperiodic in the sense of Mozes (T4); the mild/strong caveat in
  one sentence (T5) [1711.03401 L8 register].
- Homochirality (T6) and the strictly-chiral statement (T7).

## 8 Mechanization and the limit-periodic corollary (≈ 1,200)
- What Lean checks: the finite theorems (Table 1), the spine, the `Hypotheses` record (Table 3, count
  at the pinned state) and the honest sentence (T12); the `native_decide` hook listed (M2, Table 4);
  the negative controls (M5); the discharge programme and its marked admissions (M2b); the review
  record (M8); "Code." paragraph (M7).
- The limit-periodic corollary (L1–L7): the finite theorem, the fixed-point statement, the precise
  citations, the contrast sentence with the hat (Q15), Fig 8.1; hull membership open.

## 9 Remarks and open problems (≈ 700; hat §7 shape; audience's language)
- P1–P8 as questions (ledger "Open problems"), plus P9: whether the same design test (a contact rule
  that survives coarsening) yields einsteins in other crystallographic settings and dimensions (H12).
- The closing deflationary paragraph [2303.10798 L262]: the features are 1/10000 of the tile (O1);
  whether a simpler solid exists (N4).

## Appendices
- A. Data and replay in 60 s (APPENDIX_DATA.md). B. Census tables. C. Lean statement listing and
  axiom lines; the `Hypotheses` fields with their formal statements. D. The 2D calibration.

## Acknowledgements and apparatus (D6, H13)
- Tools and reviewers by role (external adversarial reviewers; automated review agents); the
  framework is cited in §3.3 only and not named here; keywords: Aperiodic monotile, einstein problem, strongly aperiodic tilings, tilings of three-dimensional space, polyhedral tiles, substitution tilings, hierarchical tilings, limit-periodic model sets, computer-assisted proof, Lean 4 formalization, Six Birds Theory, emergence calculus; MSC 05B45, 52C22, 52C23; CC BY.
