# CLAIMS_LEDGER.md — every claim the paper will make, with its evidence and tier

WRITING_PLAN.md step 5. Rule: no sentence enters the paper without a row; a row's evidence is
the artifact that produces the fact, not a document that repeats it. Columns: id, statement
(as the paper will say it, compressed), tier, evidence (file / theorem / label / citation with
line), paper section (per PAPER_PLAN.md §3). Tier codes: T1 kernel-checked Lean proof using only
standard axioms; T1n kernel-checked Lean proof with recorded native compiler hooks;
T1s retired at the re-pin because `Hypotheses` is empty; T2 Python replay;
T3 written proof or cited import (label in `proof/`); C cited external result
(theorem number given); D definition; Q quotation.

Pinned to: commit d90313a717 (2026-09-10; `Hypotheses` empty, `r44_einstein` unconditional, 21 named hooks, 23 finite theorems; re-pinned from dd2735d9bd per DECISIONS.md Q-K, step 19). Lean results are cited by declaration name; line numbers are not evidence. Frozen digest: see the last line of this file.

## Q. Quotations and attributions about other work

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| Q1 | Socolar–Taylor pose the target: "a single, simply connected 2D or 3D prototile that forces maximal nonperiodicity by shape alone, or one that does not permit any weakly nonperiodic tilings" | Q | `1009.1419 L88` | 1.1 |
| Q2 | Kaplan 2025: SCD "cautionary tale"; "demand a strongly aperiodic 3D monotile, one that admits tilings whose symmetries never include an infinite cyclic subgroup of any kind"; "personally I am daunted by the prospect" | Q | `2509.12216 L246–L254` | 1.1 |
| Q3 | The hat's definitions of weakly/strongly periodic and aperiodic; "Following Mozes" | Q | `2303.10798 L34, L64`; Mozes Invent. Math. 128 (1997) | 1.5 |
| Q4 | In the plane weak and strong aperiodicity coincide for normal tiles (GS16 Thm 3.7.1) | Q | `2303.10798 L34` | 1.1 |
| Q5 | Coulbois et al.: weakly/mildly/strongly aperiodic by stabilizer; "strongly aperiodic monotiles are unknown in all settings"; the hat is mildly aperiodic | Q | `2409.15880 L43–L45, L88, L234, L236` | 1.1, 1.5, 9 |
| Q6 | Socolar–Taylor's 3D tile: enforces R1/R2 by shape, genus zero after shifting plugs, "corrugated slabs … stack periodically"; "weakly nonperiodic tiling by Goodman-Strauss's definition" | Q | `1003.4279 L171`; `1009.1419 L69–L71` | 1.1 |
| Q7 | SCD tile, named "Schmitt–Conway–Danzer biprism" as the hat paper and Kaplan name it: a rhombic biprism, convex (decorating it with chiral plugs "loses the appealing property of convexity"), twisted layers, screw symmetry, reflections allow a periodic tiling, "heterogeneously periodic"; history: Schmitt's unpublished 1988 deformed cube and Conway's smoothing (Radin, who names neither Danzer nor Senechal nor convexity); details cited through Senechal §7.2 as the hat paper does (Senechal's text not in the corpus) | Q | `2303.10798 L33`; `2509.12216 L246–L249`; `1009.1419 L14–L16, L23, L30, L72`; `2008.09085` (dossier kaplan_radin_maiti.md); Sen96 §7.2 via SMKGS24 | 1.1 |
| Q8 | Greenfeld–Tao: translational, "sufficiently large d", "extremely large", Z³ open, tile "need not be connected"; they file the hat separately; Greenfeld–Kolountzakis: the tile can be connected | Q | `2211.15847 L5, L24–L28, L34, L600–L603`; Annals 200 (2024) 301–363; `2303.10798 L35` (GK23 connected) | 1.1 |
| Q9 | Hat: closed topological disk, needs reflections; two proofs; 188 patches cross-checked by two implementations; fault lines open | Q | `2303.10798 L13, L51–L54, L158, L253` | 1.1, 1.4, 9 |
| Q10 | Spectre: definitions of homochiral tiling and strictly chiral aperiodic monotile; unique hierarchy ⇒ non-periodic (GS16 Thm 10.1.1) | Q | `2305.17743 L22, L43, L45` | 1.5, 7 |
| Q11 | Goodman-Strauss: unique decomposition is the load-bearing property; existence by compactness | Q | `1608.07165 L80, L308` | 1.3, 6 |
| Q12 | The near-misses and what each concedes, in the hat's words: Gummelt overlaps; Penrose 1+ε+ε² ("no matter how thin or small they become, the other tiles remain necessary"); Taylor–Socolar markings, or a disconnected tile / cutpoints / a 3D shape tiling a thickened plane; Walton–Whittaker orientational rules; Mampusti–Whittaker: "not an einstein in the technical sense" | Q | `2303.10798 L28–L32`; `1903.01158 L11` | 1.1 |
| Q13 | Fletcher: one cubic prototile tiles R³ aperiodically with a 1-corona atlas rule, MLD to Kari's Wang cubes | Q | `1003.4909 L45–L48` | 1.1 |
| Q14 | Jeandel–Rao / Labbé computation-section forms ("a kind of certificate"; "impossible without a computer"; "Code." paragraph) | Q | `1506.06492 L94`; `1808.07768 L51, L253` | 1.4, 8 |
| Q15 | Socolar 2023 contrast: hat quasicrystalline vs Taylor–Socolar limit-periodic with peaks 2^{-n}k₀ | Q | `2305.01174 L137` | 8 |
| Q16 | Lee–Moody 2001 Theorem 3, four-way equivalence and hypotheses | Q/C | `math0002019 L123–L127`; Discrete Comput. Geom. 25 (2001) | 8, App. |
| Q17 | Schlottmann's theorem (regular model set ⇒ pure point) | C | `math0002019 L108`; `0910.4450 L392–L397` (LMS03 Thm 5.11/5.12) | 8 |
| Q18 | "limit-periodic" as a term (countably, not finitely, generated Fourier module; p-adic internal space) | Q | `math-ph9901008 L10, L121`; `1007.0707 L3, L49–L50` | 8 |
| Q19 | Akiyama–Lee: 168-prototile Taylor–Socolar substitution, overlap coincidence, cost disclosed | Q | `1212.4209 L48, L62–L64` | 8 |
| Q20 | Myers's Lean staging repository for the hat/Spectre (in progress, not mathlib) | C | github.com/jsm28/AperiodicMonotilesLean (web scan) | 8 |
| Q21 | History in the hat's order: Wang 1961, Berger 1966 (20,426 tiles), Robinson 1971 (six tiles), Penrose 1978 (two tiles), Jeandel–Rao (11 Wang tiles is the minimum for Wang tiles; the six/two counts use other motions and conventions) | Q | `2303.10798 L18–L24, L36, L253` (Robinson "six shapes"); `hat_references.txt` entries Wan61, Ber66, Rob71, Pen78, JR21 | 1.1 |
| Q22 | Reader-engagement sentence pointing to the interactive viewer | Q | `2303.10798 L96`; `viewer/index.html` | 3 |
| Q23 | The problem is posed by Socolar–Taylor (Q1) and described by Kaplan as demanded (Q2); the paper does NOT call it "longstanding" or "open" in anyone's words but theirs | Q | Q1, Q2; dossier `kaplan_radin_maiti.md` (Kaplan never says "open") | 1.1 |
| Q24 | Hilbert's 18th problem, second part, asked whether anisohedral polyhedra exist in R³; Reinhardt found one; Heesch gave a planar example | Q | `2303.10798 L37–L39` | 1.1 |
| Q25 | After the hat and Spectre: simplified proofs (Akiyama–Araki) and the structure of the tilings (Baake–Gähler–Sadun; Baake et al. diffraction; Socolar), one sentence | C | the papers' own abstracts: `2307.12322` (AA25), `2305.05639 L1–L14` (BGS25), `2502.03268` (BGMM25), `2305.01174` (Soc23); dossiers | 1.1 |
| Q26 | In the hyperbolic plane weak aperiodicity comes readily: Böröczky's weakly aperiodic monotile (1974); Goodman-Strauss's strongly aperiodic set (2005) | Q/C | `2303.10798 L33` (Böröczky, "appear readily in the hyperbolic plane"); GS05 title/abstract (`GS05_hyperbolic.lines`) | 1.1 |

## T. The theorem

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| T1 | Q admits a tiling of R³ | T1n (unconditional) | `r44_einstein`, first conjunct `Nonempty (Tiling Q)` (`R44/LogicalSpine.lean`) | 1.2, 3 |
| T2 | For every tiling T, Per(T) = {0} | T1n (unconditional) | `r44_einstein`, `Per T = {0}` | 1.2, 7 |
| T3 | For every tiling T, \|Sym(T)\| ≤ 24 | T1n (unconditional) | `r44_einstein`, `encard ≤ 24` | 1.2, 7 |
| T4 | No tiling has a symmetry of infinite order; hence Q is strongly aperiodic (Mozes/hat sense) | derived | T1 (existence) + T3 (every tiling has finite symmetry group) + a finite group has no infinite-order element; definition Q3 | 1.2, 7 |
| T5 | In the taxonomy of CGGL24, Q is mildly aperiodic; trivial stabilizers not claimed | derived | T1 (existence) + T3 (every tiling has finite symmetry group) + Q5 (definition: mildly aperiodic = every cotiler has finite stabilizer; Q has no self-symmetry, O5, so stabilizer = symmetry group); N3 | 1.1, 9 |
| T6 | Every tiling is homochiral; all placements +1 or all −1; no mixed pair | T1n (unconditional) | `tiling_homochiral`, `tiling_chirality_corollary` | 7 |
| T7 | Q is a strictly chiral aperiodic monotile of R³ (Spectre definition) | derived | T1 (existence) + T2 (every tiling non-periodic) + T6 (every tiling homochiral) + Q10 (definition: a tile that admits only homochiral non-periodic tilings); an all-orientation-reversing tiling is homochiral since any two copies are related by the orientation-preserving relative motion h g⁻¹ | 7 |
| T8 | Each tiling carries, at every level n, a unique partition of the registered cells into 2ⁿ-scaled chairs in registered poses, nested through the eight child poses; level 0 is the carrier tiling | T1n (unconditional), for arbitrary geometrically nested registered families | `carrier_hierarchy`, `carrier_hierarchy_unique`, `geometric_hierarchy_canonical`, `geometric_hierarchy_unique`, `carrierHierarchy_geometric` (LogicalSpine.lean at the pin; M9 closed) | 6 |
| T9 | No exhaustion clause; non-exhausting hierarchies occur (L10) and are not thereby excluded from the substitution hull; hull membership of every tiling open | N / T2 | ruling R7, MECHANIZATION_PLAN.md C3; L10 | 6, 9 |
| T10 | Reflections allowed; no face-to-face, lattice, common-orientation, connected-contact-graph or local-finiteness assumption | D | `Tiling Q` over `RigidMotion`; THEOREM.md statement | 1.2 |
| T11 | Local finiteness is proved, not assumed | T1 | `local_finiteness` (`R44/LogicalSpineFoundation.lean`), A-L2.1 | 1.5, 4 |
| T12 | The `Hypotheses` record, whose fields quoted the written lemmas one by one, is empty at the pin: all 19 former fields are theorems in `lean/R44/R44/Proved/`; `r44_einstein` takes no hypothesis and the conditional form survives as `r44_einstein_of_hypotheses` over the empty record; the theorem is kernel-checked modulo the 21 named compiler hooks; the written proofs remain as exposition | D | `lean/R44/HYPOTHESES.md` (Discharged table; Remaining fields: empty) and `LogicalSpine.lean` at d90313a717; `lean/R44/PAPER_UPDATES.md` §1–§3 | 1.4, 8, App. C |
| T13 | Period halving p/2ⁿ ∈ Z³ ⇒ p = 0; the 24-frame injection; proved outright in Lean | T1 for `no_period` and the conditional `sym_card_le_24`; T1n for period halving and their application to Q | THEOREM.md "Lean spine" paragraph; `no_period`, `all_periods_grid` | 7 |
| T14 | Parameter family: heights c_j/10000 with the R§11 conditions; proof unchanged; no perturbation stability claimed | T3 | R§11 | 9 |

## O. The object

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| O1 | Q = seven-cube chair (2×2×2 minus a corner) with 24 exposed unit panels, 8 pyramids per panel, heights ±j/10000, j=1..12, base half-width 1/100; rational coordinates; volume 7 | T1n | `solid_mesh_exact`; `solid/r44_solid.json` sha256 f320d7a0… | 2 |
| O2 | 2,138 vertices, 6,408 edges, 4,272 triangles; V − E + F = 2 | T1n | `boundary_sphere` (`R44/Theorems.lean`) | 2 |
| O3 | Boundary is a closed connected triangulated surface; every edge in two triangles; single-cycle vertex links | T1n / T2 | `boundary_sphere`; `verify/boundary_sphere.py` | 2 |
| O4 | Q is a closed topological 3-ball | C | O3 + classification of closed surfaces + PL Schoenflies (Moise; Rourke–Sanderson), cited T3 | 2 |
| O5 | Q has no self-isometry | T1n (components T1 / T1n / T1 at the pinned commit) | reduction of an arbitrary self-isometry to a carrier-preserving motion: `planar_area_carrier_recovery_holds` (T1, formal proof by diameter endpoints; the planar-area argument is the written proof, ERRATA E5); carrier-preserving motion to a feature-table frame: `carrier_feature_frame_reduction_holds` (T1n, hooks `profile_canonical`, `transported_role_geometry`); the 48-frame comparison: `no_native_symmetry` (T1); assembly `native_asymmetry_reduction` | 2 |
| O6 | 192 feature roles with distinct eighth-grid centres; 24 deviations distinct (10000 i² = 20000 j² + j⁴ unsolvable) | T1 | `native_features_length`, `native_feature_centers_nodup`, `deviations_distinct` | 2, 4 |
| O7 | Every mesh edge has a declared dihedral; 1,536 feature edges, 32 per class | T1n | `mesh_angle_audit` | 4 |
| O8 | Eight child poses partition 2P as integer cell sets | T1 | `children_partition_2P` | 3 |
| O9 | Volume 7 | T1n | `solid_mesh_exact` | 2 |
| O10 | Q is not convex | T2 | `paper/scripts/nonconvex_witness.py` (stdlib, exact rationals): the mesh vertices u = (2,2,1) and v = (2,1,2) are in Q (Q is closed and contains its boundary mesh), their midpoint m = (2,3/2,3/2) is outside Q by an exact ray-parity test along the generic direction (1,1/7,1/11) with 0 proper crossings and 0 boundary hits, after an exact check that m lies on no closed triangle of the surface (0 of 4,272), controls (1/2,1/2,1/2) inside and (3,3,3) outside; output `STATUS: PASS` | 1.1, 9 |
| O11 | Planar boundary areas of Q on the nine coordinate planes: 2492/625 at height 0, 623/625 at height 1, 1869/625 at height 2 (each axis), each > 9/10; all non-axis facets together < 1212/15625 < 1/4; the three area types identify the height-0, height-1 and height-2 plane triples, so a self-isometry fixes the origin, the corner (2,2,2) and the notch, hence P | T2 (areas) / T3 (the written lemma `planar_area_carrier_recovery`) | `paper/scripts/planar_areas.py` (stdlib, exact rationals from `solid/r44_solid.json`; `STATUS: PASS`); external review 2026-09-09 m2 | 2 |
| O12 | Figures 1 and 3 are exaggerated illustrations of Q, not true-scale renderings: the seven-cube carrier and all 192 feature centres at their canonical coordinates, feature bases widened ×5 about their centres, signed heights ×80, polarities and relative heights preserved, no feature added, omitted or moved; panel 13 (outward normal −y, centre (3/2, 0, 3/2), global tangent axes x, z) carries roles 104–111 with signed coefficients −9, −10, −11, −12, +9, +11, +10, +12 (true height a/10000, true base side 1/50); the sections show its +9 and −9 features | D | `figures/print-preview/build_preview.py` (192/192 feature records checked against the mesh and `solid/native_panels.csv`, rational arithmetic), `audit_preview.py` (768 display triangles read back), `feature-audit.csv` rows 104–111, `visibility-audit.csv`, `SHA256SUMS`; owner-supplied artwork 2026-09-09 replacing the `render_r44.py` renders in Figures 1 and 3 | 1, 2, A |

## D. Definitions and public wording

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| D1 | Tile, tiling, admits, monohedral (congruence includes reflections), locally finite | D | Grünbaum–Shephard via `2303.10798 L57–L58`, with "closed topological disk" replaced by "closed topological 3-ball" | 1.5 |
| D2 | A monotile is a tile admitting a monohedral tiling; an aperiodic monotile or einstein here is a closed topological 3-ball admitting tilings but only non-periodic ones, by geometry alone, with no non-geometric matching rule | D | `2303.10798 L25` restated for 3-balls | 1.5 |
| D3 | Registered, registration, the atlas, features, panels, carrier, supertile of level n | D | our definitions in §2–§3 from `solid/r44_solid.json`, `certificates/candidate_certificate.json`, `LogicalSpine.lean` (`Registration`, `RegisteredPose`, `CarrierHierarchy`) | 2, 3, 6 |
| D4 | Public qualifier: "proof submission" until the written lemmas are formalized or refereed | D | `README.md` L9–L12 and the review-status paragraph; HANDOFF.md §5 | 8, front matter |
| D5 | Homochiral tiling; strictly chiral aperiodic monotile | D | `2305.17743 L22` verbatim | 1.5, 7 |
| D6 | Apparatus: keywords "Aperiodic monotile, einstein problem, strongly aperiodic tilings, tilings of three-dimensional space, polyhedral tiles, substitution tilings, hierarchical tilings, limit-periodic model sets, computer-assisted proof, Lean 4 formalization, Six Birds Theory, emergence calculus" (owner, 2026-09-09); MSC 05B45, 52C22, 52C23; CC BY; DOI/arXiv/URL on every reference; "Code." paragraph | D | COMMUNITY_PAPER_PROFILE.md §2 item 7, §7 | front/back matter |
| D7 | The chirality/congruence convention paragraph, then that Q needs no such caveat | Q/derived | `2303.10798 L52–L54`; T6 | 1.2 |
| D8 | The planar calibration (Appendix D): the hat reconstructed as an exact polygon with its published substitution and recognition grammar replayed as imports; an abstract Lean theorem (`CoarseningTower`, `period_lifts`, `tower_forces_trivial_stabilizers`, `nonempty_tower_landing`) that transports a period unchanged through coarsening levels and excludes nonzero periods by unbounded lower bounds; a tooling calibration, not a result, and not the R44 halving normalization | D | `calibration_2d/LANDING.md`; `calibration_2d/rounds/r004_varying_geometry_tower/formal/Tower.lean` | App. D |
| D9 | Patch: a finite subfamily of a packing, without the hat's topological-ball condition; 1-corona: the tiles touching a chosen tile; cut-and-project scheme, model set, regular model set, 2-adic internal group, modular coincidence as in Lee–Moody | D | `2303.10798 L61` (hat patch convention); `1003.4909 L25` (Fletcher 1-corona); `math0002019 L102–L107` (Lee–Moody definitions), `L31–L32` (modular coincidence), `L111–L115` (the completion and the cut-and-project construction) | 1.5, 8 |

## H. How the tile was found (source: DISCOVERY.md; framework never evidence; THEORY SIGN-OFF required)

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| H1 | Periodicity as descent, at the symbolic level: a lattice labelling x : Z³ → A is p-periodic iff it factors through Z³/⟨p⟩ (elementary, one line). Bridge to tilings of Q, stated only as far as the pinned declarations go: every tiling admits a registration (`registration_of_tiling`: one ambient isometry after which every placement is one of the 24 proper cubic frames plus an integer shift; T1n through `unrestricted_alignment_holds` (A15), `component_solids_cover_holds` (A14), `baseline_component_covers_grid_holds` (A13)), and under registration plus native asymmetry (`NativeAsymmetric Q`, T1n: assembled by `native_asymmetry_reduction` from `planar_area_carrier_recovery_holds` (R§6 / E5, T1), the carrier-frame reduction `carrier_feature_frame_reduction_holds` (T1n) and the 48-frame comparison `no_native_symmetry` (T1)) every translational period of the tiling is an integer vector in the ambient frame (`period_grid_from_registered_poses`, which requires `NativeAsymmetric Q`). This is the one direction the proof uses; no packaged equivalence between geometric periods and the periods of a 168-label encoding is claimed or cited. An einstein is a rule with admissible global labellings none of which descends; for Q the conclusion Per(T) = {0} is derived directly, by period halving (`period_halving`) and integrality at every level (`r44_einstein`) | elementary (symbolic part) + T1n bridge by named declarations | one-line proof; `registration_of_tiling`; `period_grid_from_registered_poses`; `period_halving`; Foundations VI L2010–L2020 for the phrasing | 1.3 |
| H2 | Theorem G11 verbatim (two hypotheses, conclusion); calibration list ending with the hat and Spectre; role reading P2/P4/P1 | Q | Foundations VI L2044–L2056, L2086–L2096, L2102–L2106; doi:10.5281/zenodo.22254289 | 1.3 |
| H3 | A hierarchy certifies aperiodicity only if forced: equivariant extraction preserves stabilizers; recognizability + unique composition + period halving | Q / elementary | `1608.07165 L80, L308`; `2305.17743 L43`; the stabilizer inclusion Stab(x) ⊆ Stab(q(x)) (one line, stated) | 1.3 |
| H4 | One shape puts the admissibility rule into the carrier; three requirements for a marked system to become a bare solid (existence; every geometric realization decodes; a geometric period is a decoded period); "one shape ≠ one role" | D | P3/P4/P5 `SOURCE_AUDIT.md` "SBT interpretation"; `history/cascade/findings.md` L44 | 1.3 |
| H5 | The design test (a diagnostic, not a theorem): the halving argument needs the coarsened tiling to be again a legal tiling of Q, i.e. the decoded parent contact language must lie inside the fine language; equality of the two languages is the sufficient form that is checked, finite form for Q `parent_atlas_eq_fine`. Sufficient, not necessary (a strictly smaller decoded language would also preserve legality). When the decoded language is strictly larger the argument fails and whether a periodic parent tiling exists must be checked; in the one case that arose (P4) it existed, for that case's language only | T1n (the identity) / D (the test) | `parent_atlas_eq_fine`; R§8; P4 `PROOFS.md` L104–L139 | 1.3, 3.2 |
| H6 | The framework supplied the reading and the test, not the proofs; framework vocabulary certifies nothing; claims are instrument-indexed; no literalization | D | non-descending-objects paper (dossier D §5: "This vocabulary alone does not certify any claim"; no-overreading theorem) | 1.3, 8 |
| H7 | Step 1: the marked chair: a single-marking local rule admits the chair substitution and no periodic tiling up to L = 7 (SAT); the all-scale recursion is recorded as an honest gap; the marks could not be geometrized | D (history, finite evidence only) | `history/cascade/findings.md` L40–L48; `LINEAGE.md` item 1 | 3.3 |
| H8 | Step 2: first bare solid is a periodic control; 62 fine contacts decode to 398 parent contacts | T2 (packet replay) | P3 `README.md`; P4 `PROOFS.md` L106, L136; P4 `README.md` | 3.3 |
| H9 | Step 3: the frame change; 44 = 44 with the full 24-element frame group | T1n | P5 `PROOFS.md` "Claim and evidence status"; `parent_atlas_eq_fine`, `orientation_group_24` | 3.3 |
| H10 | The method proves neither existence nor alignment; existence, forced asymmetry and selection are separate achievements | D | P1 `HANDOFF_PROMPT.md` discipline sentence; STATEMENT.md | 3.5 |
| H11 | G11 instantiation for the registered system C_44, carried to Q by registration (A15) and the small-collar realization (R10): [H-G11-nonempty] = T1; [H-G11-hierarchy] (i) uniqueness at every scale = T8 (T1n, arbitrary geometrically nested registered families, `geometric_hierarchy_unique`), (ii) local forcing = Theorem 7.1 level by level (`parent_local_to_global`, R6, with `parent_atlas_eq_fine`, R7; radius growing with level; NOT local derivability from the unlabelled chair, N2), (iii) the period clause is reached by the halving tower (T13), not by per-period finite certificates, which the proof does not extract; conclusion = T2 | derived (T1n throughout: existence, hierarchy, local forcing, registration bridge and period exclusion are unconditional Lean theorems at the pin) | DISCOVERY.md §1b; T1, T2, T8, T13, R6, R7, R10, A15 | 1.3, 3.3 |
| H12 | Open problem: the same design test in other crystallographic settings and dimensions | N | — | 9 |
| H13 | Disclosure of AI use ("Use of AI systems", after the acknowledgements): the solid was found by an OpenAI reasoning model (ChatGPT, Astra) given the Six Birds framework and the construction record (the framework was the input); the earlier construction record and the Lean/certificate work by automated agents (Codex implementer; Grok and Codex-on-a-second-model reviewers; two external adversarial rounds); the manuscript largely written by Claude Fable 5.1 under the author's direction and reviewed by Codex gpt-6-astra; no AI system is an author | D | owner statement 2026-09-09; `LINEAGE.md` packet table; `provenance/HASH_CHAIN.md`; `lean/R44/MECHANIZATION_PLAN.md` agent roles; `paper/review/PROTOCOL.md`; `.codex/logs/reviewer/` | back matter, 3.3 |
| H14 | Provenance: the tile was landed in six hash-chained packets, each naming or embedding its predecessor by sha256, with the solid identical in packets 5 and 6; every packet's manifest and stdlib replay verified in the fusion; steps 2–3 of the discovery are packets 3–5, the alignment proof packet 6 | D | `provenance/HASH_CHAIN.md`; `LINEAGE.md` (packet table) | 3.3 |

## A. Part A — every tiling is grid-registered (ALIGNMENT_PROOF.md, A-labels)

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| A1 | Local finiteness (A-L2.1) | T1 | T11 | 4 |
| A2 | Cone / sector budgets (A-L2.2) | T1n | `cone_sector_budgets_holds` (Proved/) | 4 |
| A3 | Complete dihedral list (A-L3.1) | T1n (+T1 arithmetic) | `complete_dihedral_list_holds` (Proved/; hooks `native_mesh_incidence_trace`, `carrier_coordinate_states_table`, R8/R10); `deviations_distinct` | 4 |
| A4 | Generic feature-edge point has exactly one complementary partner (A-L3.2) | T1n | `generic_feature_partner_holds` (Proved/; exceptional-vertex table hooks) | 4 |
| A5 | Circular-cone formula at L = 3/25 (A-L4.1, arithmetic half) | T1 | `circular_cone_solid_angle_holds` (Proved/) | 4 |
| A6 | Feature circular-cone containment (A-L4.1, geometric half); Ω(L) > 4π/3 ⟺ 8L² < 1 | T1n / T1 | `feature_circular_cone_containment_holds` (Proved/); `coneAngle_gt_four_pi_div_three_iff` | 4 |
| A7 | One tile accompanies the whole feature graph (A-T4.2) | T1n | `connected_feature_companion_holds` (Proved/) | 4 |
| A8 | Containment ⇒ equal features, edge-length rigidity (A-L4.3) | T1n (formal proof by compactness, not the written length count) | `feature_containment_rigidity_holds` (Proved/; with g ≠ h, L5X) | 4 |
| A9 | Companion pose ∈ signed permutations × (1/8)Z³ (A-C4.4) | T1n | `companion_pose_discrete_holds` (Proved/; side condition `mate_records_roles_nonempty`, R8) | 4 |
| A10 | Eighth-grid baseline overlap ⇒ core overlap (A-L5.1); the written estimate gives box side ≥ 21/200 | T1 for the overlap implication (`retained_core_overlap_holds`); T3 for the written quantitative estimate (A-L5.1, `proof/ALIGNMENT_PROOF.md`) | `retained_core_overlap_holds` (Proved/); A-L5.1 | 5 |
| A11 | Companion census: 6,862 formula poses; 1,545 collide with the root directly; 5,317 isolated (5,234 fractional, 83 integral); 5,273 rejected by companion-option collisions; 299,975 option collisions; 44 survivors equal to the atlas as a set; two independent Python implementations | T1n / T2 | `mates_census`; `verify/packets/r44_unrestricted_alignment/results/alignment_verification.json` (`complete_feature_mates`); `verify/replay.py` (two implementations, `verify/packets/*`) | 5, App. B |
| A12 | Only the 44 registered mates occur (A-L5.3) | T1 | `only_registered_mates_holds` (Proved/) | 5 |
| A13 | A feature component's baseline cells = Z³ (A-L6.1) | T1n | `baseline_component_covers_grid_holds` (Proved/) | 5 |
| A14 | The component's tiles cover R³ (A-L6.2) | T1 (formal proof by clamping to an interior point, not assembly-wide gluing) | `component_solids_cover_holds` (Proved/) | 5 |
| A15 | Unrestricted alignment: every tiling is registered (A-T6.3) | T1n | `unrestricted_alignment_holds` (Proved/); `registration_of_tiling` | 5 |
| A16 | Tube construction: per-tube homeomorphisms, gluing, image = Q (A§1) | T1n | `per_tube_homeomorphisms_holds`, `feature_tube_maps_glue_holds`, `feature_tube_map_carries_carrier_holds` (Proved/); disjointness and boundary identity proved (T1) | 2, App. |
| A17 | Errata E1, E3, E6 carried into the text | T3 (text); the corrected lemmas are T1n/T1 (A8, A4, A14) | `proof/ERRATA.md` | 4, 5 |

## R. Part B — the registered theorem (PROOFS_registered.md, R§)

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| R1 | 21 internal contacts refine to a 30-state closure; 372 sign equations; 12 balanced components; canonical profile | T1n | `contact_closure_30`, `profile_canonical` | 3 |
| R2 | 2,388 shell poses in 48 frames → exactly the 44-contact atlas | T1n | `atlas_44` | 3, 5 |
| R3 | 19 contact frames generate the 24-element proper cubic group | T1n | `orientation_group_24` | 3, 7 |
| R4 | 33 first shells (exact covers of the 22-cell shell), each with one candidate parent signature | T1n | `first_shells_33` | 6 |
| R5 | 14 of 32 outer-root shells completable, 18 not; centre typed central | T1n | `central_completion` | 6 |
| R6 | All 28 parent pairs conflict ⇒ unique parent (T7.1); local-to-global proved | T1n (unconditional) | `parent_conflicts_28`; `registered_first_shells`, `certified_shells_complete_parents`, `complete_parent_conflicts`, `parent_local_to_global` | 6 |
| R7 | 697 → 116 → 44 parent contacts, all even; halved = fine atlas; coarsening preserves admissibility (T8.1); common parity; halved baseline tiling | T1n (unconditional) | `parent_atlas_eq_fine`; `parent_atlas_admissibility`, `parent_common_parity`, `halved_parent_baseline_tiling` | 6 |
| R8 | Same-frame grandchild at (2,2,2); nested controls 64/4,096 poses, 448/28,672 cells | T1n | `nested_substitution_controls`, `hierarchy_cell_controls` | 6 |
| R9 | Registered shell cell controls (192 features → 22 shell cells; legal frames among 48) | T1n | `registered_shell_cell_controls` | 5 |
| R10 | Small-collar realization: a baseline chair tiling with matching profiles is carried to a Q-tiling by the glued tubes (E2, E6) | T1n (formal proof identifies duplicate tube sites by centre; separation 21/200) | `small_collar_realization_holds` (Proved/) | 3, 6 |
| R11 | Erratum E4 (half-integer coset after halving; periods still in Z³) | T3 | `proof/ERRATA.md` E4 | 7 |
| R12 | Erratum E5 (the native-asymmetry statement is split into carrier recovery, frame reduction and the 48-frame comparison; tiers as in O5: T1 / T1n / T1 at the pinned commit) | D | `proof/ERRATA.md` E5; O5 | 2 |

## L. Limit-periodic corollary (ruling R7)

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| L1 | The 168-label lattice substitution is total; matrix column sum 8; least primitive exponent 3; least modular-coincidence depth 3 at a=(0,0,2), i=78 | T1n / T2 | `substitution_modular_coincidence` (`Theorems.lean`, by declaration name); `verify/substitution_modular_coincidence.py` | 8 |
| L2 | The coincidence check ranges over all 168 starting labels (not diagonal) | T2 | replay: `states = [(ORIGIN, frozenset(range(168)))]` | 8 |
| L3 | A legal two-sided fixed point exists: a substitution-fixed labelling of Z³ is determined by its 2×2×2 seed block on {−1,0}³, each label fixed by its residue map; the substitution language contains exactly 27 fixed seed blocks, in proper-rotation orbits of sizes 24 and 3; every seed reproduces itself in place under iteration, so its iterates labell all of Z³ with every finite patch legal; every finite patch occurs inside a refinement of the native chair (primitivity), so the encoded chair poses form a registered chair tiling with all contacts in A₄₄ and small-collar realization gives a tiling T_w by Q. (Earlier draft: 24, from a level-3 search; corrected by the external manuscript review 2026-09-09, B1.) | T1n (`seed_language_closure`: closure sizes, 27 seeds, orbits 24 + 3, histogram {1:24, 8:3}, in-place reproduction, frame commutation) / T2 / written (seed → tiling) | `R44.seed_language_closure` (Theorems.lean at the pin; landed 6a7e7a4c9a); replay step `seed_language_closure` in `verify/replay.py`; `paper/scripts/seed_language_closure.py` (stdlib; reconstructs φ from `certificates/candidate_certificate.json` through `verify/substitution_modular_coincidence.py`; exact closure of the 2×2×2 block language 168 → 600 → 1,278 → 1,398 → 1,410, stable; `STATUS: PASS`); `paper/review/external_2026-09-09/` (reviewer's independent audit, same numbers) | 8 |
| L4 | PF eigenvalue 8 = \|det 2I\|; label classes of a fixed point partition Z³ | derived | column sum 8 (L1); L3 | 8 |
| L5 | Label classes are regular model sets with 2-adic internal space; pure point diffractive | C | Q16 (iv)⇒(ii), Q17 | 8 |
| L6 | The structure is limit-periodic (term of BMS98/BG10), not quasicrystalline; contrast with the hat | C / Q | Q18, Q15 | 8 |
| L7 | Level of the statement: fixed point; hull membership of every tiling open | N | DECISIONS.md Q-A; T9 | 8, 9 |
| L8 | At depths 1, 2 and 3 the address-count distributions by possible-label-set size are {42:8}, {6:48, 24:16} and {1:336, 6:160, 24:16} (all addresses tracked from the full label set) | T2 | `verify/substitution_modular_coincidence.py`, output field `coincidence_label_set_sizes`; `paper/scripts/coincidence_tree.py` | 8 (Fig. 8.1) |
| L9 | Sym(T_w) is the stabilizer of the seed w in the 24-element proper cubic group G (acting on the seed cube by moving cells and composing frames): stabilizer orders 1 for the 24 seeds of the large orbit and 8 for the three seeds of the small orbit; for the seed (28,84,91,35,98,42,49,105) the stabilizer is generated by (x,y,z)↦(z,y,−x) and (x,y,z)↦(−x,−y,z). Deduction: a symmetry (R,t) has R ∈ G, t ∈ Z³ (T3 argument of Thm 7.2); parent recognition is rotation-covariant (children of a rotated pose are the rotated children, finite check) and translation-covariant (Thm 6.5), so D(gT_w) = (R,t/2) T_w = T_w forces t ∈ ∩ 2ⁿZ³ = 0; the substitution commutes with G on labelled cells (finite check), so R T_w = T_{Rw} and R T_w = T_w iff Rw = w. Hence tilings with trivial symmetry group and tilings with symmetry group of order 8 exist; Q is not strongly aperiodic in the CGGL24 sense | T1n (`seed_language_closure`: orbits and stabilizer histogram) / T2 (generators, covariance 12,096 configuration and 576 pose checks) / written (deduction) | `R44.seed_language_closure`; `paper/scripts/seed_language_closure.py` (stdlib; reconstructs φ from `certificates/candidate_certificate.json` through `verify/substitution_modular_coincidence.py`; exact closure of the 2×2×2 block language 168 → 600 → 1,278 → 1,398 → 1,410, stable; `STATUS: PASS`); external review 2026-09-09 M1 (independent argument via intrinsic ancestor classes, `paper/review/external_2026-09-09/COUNTEREXAMPLES.md`) | 8, 7, 9, 1.1, 1.5 |
| L10 | Non-exhausting hierarchies occur: the fixed point with seed (6,0,4,5,2,3,0,1) has two whole tiles in frame A = diag(−1,−1,1), at the origin (its own child 000 at every level; ancestors 2ⁿAP, union the closed octant {x ≤ 0, y ≤ 0, z ≥ 0}) and at (1,1,−1) (its own central child; ancestors fill the closure of the complement): an infinite fault surface on supertile boundaries at all levels, inside a substitution-legal tiling; its symmetry group is trivial (L9). Non-exhaustion is not exclusion from the substitution hull | T2 (poses, self-roles, stabilizer) / written (ancestor union) | `paper/scripts/seed_language_closure.py` (stdlib; reconstructs φ from `certificates/candidate_certificate.json` through `verify/substitution_modular_coincidence.py`; exact closure of the 2×2×2 block language 168 → 600 → 1,278 → 1,398 → 1,410, stable; `STATUS: PASS`) (w0 block: poses, self-roles [0] and [7], stabilizer 1); external review 2026-09-09 M1 | 6, 8, 9 |

## M. Mechanization and computation (disclosure rows)

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| M1 | 23 finite theorems in Lean; method per theorem (`decide` / `native_decide`) | T1/T1n | `lean/R44/AXIOMS.md` decision-method ledger; `Theorems.lean` | 8, App. C |
| M2 | `r44_einstein` axiom line: `propext, Classical.choice, Quot.sound` plus 21 named `native_decide` hooks: the 15 of the phase-1 finite theorems (atlas_44, central_completion, contact_closure_30, first_shells_33, hierarchy_cell_controls, mates_census, mesh_angle_audit, nested_substitution_controls, orientation_group_24, parent_atlas_eq_fine, parent_conflicts_28, profile_canonical, registered_shell_cell_controls, solid_mesh_exact, transported_role_geometry; the last is an auxiliary check in `Proved/CarrierFeatureFrameReduction.lean`, not one of the 23 finite theorems of `Theorems.lean`, so the hooks cover the finite computations used by the proof including that auxiliary check) and six closed checks over certified data made by the discharge proofs (mate_records_roles_nonempty R8; native_mesh_incidence_trace R8; carrier_coordinate_states_table R10; feature_index_bounds, feature_vertex_lookup, carrier_vertex_lookup); no `sorryAx` anywhere | T1n (unconditional) | the `'R44.r44_einstein' depends on axioms` line of `lean/R44/build_axioms.log` (at the pinned commit; verbatim in APPENDIX_DATA.md §5) | 8, App. C |
| M2b | CLOSED at the re-pin: no admission remains; `R44/Discharge/` holds no module; the three declarations that carried `sorryAx` at dd2735d9bd are admission-free theorems in `Proved/`; the paper says so where it mentions the discharge programme (historical) | D | `lean/R44/AXIOMS.md` at d90313a717 (`sorryAx` nowhere); controls.sh `admissions=0` | 8, App. C |
| M3 | Two independent Python implementations of the companion census; stdlib only; replay ≈ 1 minute | T2 | `verify/replay.py`; `verify/packets/r44_unrestricted_alignment`, `verify/packets/einstein_macrostate` | 8, App. A |
| M4 | No floating-point value enters any verified predicate: certificates are integer/`Fraction` data, checkers use `int` and `fractions.Fraction`, Lean decides integer literals; decimal numbers occur only as timing metadata (`"seconds"` fields, `time.monotonic()`) and in the OBJ rendering export; the paper-lane verification scripts named in Appendix A likewise use `int`/`Fraction` only, the planar-area checker bounding sqrt q by (q + m²)/(2m) with integer-square-root witnesses m, exactly | D | `certificates/candidate_certificate.json` and `companion_collision_certificate.json` (one `"seconds"` decimal each, no other decimal literal); `verify/tube_formula_controls.py:11`, `verify/packets/*/src/*.py` (`from fractions import Fraction`); `verify/packets/einstein_macrostate/src/build_solid.py:64` (the only `float(`); `Theorems.lean` (`decide`/`native_decide`) | 8 |
| M5 | Negative controls: must-fail files with checked diagnostics; scope regressions; six corrupted inputs rejected | T2 | `lean/R44/scripts/controls.sh`; `verify/packets/r44_unrestricted_alignment/src/test_mutations.py` | 8 |
| M6 | Lean 4.31.0 + Mathlib (commit at freeze); build time and peak RSS from the gate log | D | APPENDIX_DATA.md (step 8) | App. C |
| M7 | "Code." paragraph: repository, tag, license | D | step 18 | 8 |
| M8 | Review record: two external adversarial rounds (round 1 FAILS → L5X; round 2 HOLDS-AS-STATED, reviewer could not run Lean) | D | `proof/review/external_2026-09-08*/` | 8 |
| M9 | `carrier_hierarchy_unique` quantifies over `LevelSupertilePose H T n`, whose `mem` field places every level-n pose in `(coarseningIterate H n T).placements` = Dⁿ(T); CLOSED at the re-pin (formal bridge landed 44282b63e8): `GeometricHierarchy` carries raw poses with no membership; `geometric_hierarchy_canonical` proves every level-n pose lies in Dⁿ(T) by induction from unique parents; `geometric_hierarchy_unique` gives uniqueness among arbitrary geometrically nested registered families; `carrierHierarchy_geometric` the existence half; must-fail `negative/NoncanonicalGeometricHierarchy.lean` | D | pinned `LogicalSpine.lean` (LevelSupertilePose, carrier_hierarchy_unique, GeometricHierarchy, geometric_hierarchy_canonical, geometric_hierarchy_unique, carrierHierarchy_geometric); external review 2026-09-09 M2; `paper/review/external_2026-09-09/REVIEW.md` | 6, 8 |

## N. Non-claims (each must appear as a hedge where relevant)

| id | statement | § |
|---|---|---|
| N1 | Not every tiling is shown to lie in the substitution hull; non-exhaustion (L10) is not exclusion from the hull | 6, 8, 9 |
| N2 | Local derivability from the unlabelled chair is not claimed | 6 |
| N3 | No claim that the bound 24 is attained, nor which symmetry groups occur beyond the orders 1 and 8 of L9; every-tiling triviality (CGGL24 strong aperiodicity) is false for Q (L9), not open | 1.1, 1.5, 7, 9 |
| N4 | No minimality (faces, vertices, features) and no convexity | 9 |
| N5 | No decidability result | 9 |
| N6 | No perturbation stability beyond R§11 | 9 |
| N7 | No second, computer-free proof | 1.3 |
| N8 | No mathlib coverage; the theorem is checked modulo the 21 named `native_decide` hooks, not by kernel `decide` alone | 8 |
| N9 | The theorem-free periodicity search (`simulations/periodicity_search.py`; receipt `simulations/periodicity_search_report.json`, commit d90313a717) is evidence, not proof, and is used nowhere in the proof: grid-registered copies (48 frames), full-rank sublattices of index ≤ 40 (43,981, all UNSAT), coronas to radius 5 of 5 (251 copies), wall time 108,682 s; positive controls (unit cube index 1, featureless chair index 7) receipted in `simulations/review/2026-09-09_periodicity_search_r1_eddy.md` | 8 |

## Open problems (§9; each is a question, none a result)

P1 bound 24 attained; which other finite symmetry groups occur (orders 1 and 8 do, L9; CGGL24 Q32
is answered negatively for Q); P2 which non-exhausting hierarchies occur (one does, L10) and the full
tiling space (hull membership); P3 convex strongly aperiodic monotile in R³; P4 bilaterally symmetric or achiral
one; P5 fewest faces / simplest solid, the parameter family; P6 Heesch and isohedral numbers in
R³, decidability; P7 a shorter proof; P8 the mechanism in other dimensions and crystallographic
settings.

Frozen digest (sha256 of this file above this line, 2026-09-10, pinned commit d90313a717): 5ed828138081510847f5a89c53c152607138580d1cb041d4486904ccb63f49e9

## 2026-09-13 supplement: finite admissibility and contextual distinctions

Owner-authorized late section, complementary to the existing proof. The original
two-page target was relaxed on 2026-09-13 to allow a 200--300-word philosophical
close and transitions. The frozen ledger above is retained; its references to the old
Remarks section 9 now refer to section 10. The mathematical/Lean baseline stays
as recorded above. These additions have written-proof or finite-replay status,
not new Lean coverage. Review and build receipts: `review/CONTEXT_SECTION_2026-09-13.md`.

| id | statement | tier | evidence | § |
|---|---|---|---|---|
| C1 | Nine cyclic-frame pairs erase to the same carrier pair; the 24-centre profile test matches exactly on the diagonal; every off-diagonal has a strict overlap, including roles 188/4 at (5/4,11/8,1); the three root contexts distinguish all three neighbour frames | T2 + T3 | `scripts/contextual_frames.py`, canonical `solid/r44_solid.json` feature records; diagonal packing from the eight-child subdivision; success/failure separates each pair of neighbour states | 9 |
| C2 | Sufficiency closure concerns factorization of declared readouts, distinct from D preserving the legal tiling space | D + T3 | local source `provenance/sbt_papers/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex`, theorem F7; manuscript coarsening theorem | 3.3, 9 |
| C3 | Every registered tiling has coherent intrinsic parent-anchor classes modulo 2^n; phase observations have 8^n values, strictly decreasing kernels with diagonal intersection, and translation covariance | T3 | written Proposition `prop:phases` and proof in `tex/sec9_context.tex`, from common-parent parity, nested hierarchy, child 000 anchor zero; subsequent covariance argument | 9 |
| C4 | All translated-label readouts identify origins exactly modulo Per(labeling); faithful registered cell encoding identifies this with Per(T), hence every sufficient observation of probe origins is injective | T3 | written substitution u=z-v in `tex/sec9_context.tex`; frame and native cell recover owner pose; existing no-period theorem | 9 |
| C5 | Phase equality does not assert patch equality; state counts are not entropy; coherent phase need not reconstruct the tiling; no new hull/diffraction claim or exclusion of finite descriptions/coarse models | D + T3 | scope of the defined phase and readout maps; existing Section 8.2 scope | 9 |
| C6 | Contextual equivalence is the coarsest equivalence preserving the declared outcomes, including admissibility; enlarging the context family refines it, but does not alone imply strict refinement at unbounded depths | D + T3 | definition by equality of every contextual outcome in the closing discussion of `tex/sec9_context.tex`; strict phase refinement is separately C3; cross-domain extension posed only as a question | 9 |
