# DISCOVERY.md — how the tile was found, as the paper will tell it

WRITING_PLAN.md step 9b (added 2026-09-08 at the owner's request). This file is the source for the
paper's section "How the tile was found". Every claim carries its evidence in a public artifact of
this repository (the hash-chained packets under `provenance/packets/`, `LINEAGE.md`, the cascade
record under `history/`) or a citable Six Birds paper; the single exception is the labelled
authors' account that opens §1, a discovery narrative in the hat paper's §2 genre that carries no
claim (DECISIONS.md Q-G; WRITING_PLAN.md step 9b). The private discovery thread is not a source
of this file, is not quoted, and will not be cited by the paper. The method is presented as the
motivation that produced the object and the proof plan; it is never evidence, and no tier changes.
Genre precedent: the hat paper's §2 narrates "our process of discovery and analysis" and labels it
provisional (`2303.10798 L55, L69–L70`).

Sources: `P3 = provenance/packets/einstein_recursive_interface.zip`, `P4 = einstein_reverse_descent.zip`,
`P5 = einstein_r44_proof_submission.zip`, `P6 = r44_unrestricted_alignment.zip` (each with
`README.md`, `PROOFS.md`, `SOURCE_AUDIT.md`); `LINEAGE.md`; `history/cascade/findings.md`,
`history/cascade/sbt_primer_condensed.md`; Six Birds Foundations IV (F7 Sufficiency Closure, F12
No-Free-Distinction, F28 Composability; `provenance/sbt_papers/…Foundations_IV…tex`, SHA256
recorded in P3–P5 `SOURCE_AUDIT.md`) and Foundations VI, law G11 "Local-Rule Global-Anti-Symmetry"
(`../six-birds-papers/…Foundations_VI…tex`, read-only foreign directory; Zenodo
doi:10.5281/zenodo.22254289; statement copied in §1b below). The Six Birds sources and their Zenodo
DOIs are in `../six-birds-papers/` (owner's instruction 2026-09-08); six study dossiers on the theory
are in `offgit/paper_corpus/dossiers_2026-09-08/sixbirds_*.md`.

## 1. The reading that steered the construction (paper's own words)

The authors' account (a discovery narrative in the hat paper's §2 sense, not a sourced claim): the
tile was found by first asking what an aperiodic monotile *is*, in the terms of an emergence
framework (Six Birds), and then designing a solid to satisfy that description. What the public
record corroborates: the packets that produced Q name the framework as their structural compass
(P1 `HANDOFF_PROMPT.md`: "Use SBT as a structural compass, but do not replace geometric existence,
universal recognition, or proof verification by an audit status") and state their diagnoses of the
failed candidate in its terms (P3–P5 `SOURCE_AUDIT.md`). The reading, stated here in the community's
own vocabulary and without the framework's:

1. **Aperiodicity is a failed descent.** For a labelling x : Z³ → A of the lattice, x is p-periodic
   (p ∈ Z³ nonzero) exactly when x factors through the quotient Z³ → Z³/⟨p⟩. For a tiling of R³ by
   Q the bridge is registration, stated only as far as the pinned declarations go: every tiling
   admits a registration (`registration_of_tiling`, T1n through `unrestricted_alignment_holds` and the covering
   theorems): one ambient isometry after which every placement is one of the 24 proper cubic frames
   plus an integer shift; and under registration and native asymmetry (`NativeAsymmetric Q`,
   T1n: `native_asymmetry_reduction` assembles it from the carrier-recovery theorem
   `planar_area_carrier_recovery_holds` (R§6 / E5, T1), the carrier-frame reduction
   `carrier_feature_frame_reduction_holds` (T1n) and the 48-frame comparison `no_native_symmetry`
   (T1)) every translational period of the tiling is an integer vector in that frame
   (`period_grid_from_registered_poses`). That is the direction the proof uses; the paper does not
   claim a packaged equivalence between the tiling's periods and the periods of a label encoding.
   An einstein is then a rule under which legal global labellings exist but none factors through
   any nontrivial translational quotient; for Q the conclusion Per(T) = {0} is derived directly,
   by period halving and integrality at every level (`period_halving`, `r44_einstein`).
   The obstruction is productive: local pieces do globalize; what fails is globalizing them inside
   the class of periodic realizations. (Foundations VI names this pattern G11 and lists the hat and
   the Spectre as instances; Foundations IV's descent laws supply the general form.)
2. **The hierarchy must be forced, not drawn.** A grouping of tiles into supertiles certifies
   aperiodicity only if the configuration determines it and every symmetry of the configuration
   preserves it; a grouping the observer chooses (2×2 blocks on a square grid) adds information the
   configuration does not carry and proves nothing. Under an equivariant extraction a symmetry of
   the configuration is a symmetry of every extracted level; if no nontrivial translation survives
   all levels, none was a symmetry. This is recognizability plus unique composition plus period
   halving, the community's own mechanism (Goodman-Strauss `1608.07165 L80, L308`; Spectre
   `2305.17743 L43`), read as a design target rather than as a proof technique.
3. **What one shape adds.** With marked tiles the admissibility rule is external to the pieces; a
   geometric monotile puts it into what can physically fit. For a marked system to become a bare
   solid, three things must hold: a geometric realization exists; every legal geometric realization
   decodes into the intended marked system; and a period of the geometric tiling would be a period
   of the decoded system. The second requirement is the one that is easy to lose: preserving the
   intended construction is not enough, the bare solid must not admit extra periodic realizations.
   Under this reading "one shape" does not mean "one role": copies of one solid occupy different
   positions in a forced compositional structure, and the effective diversity lives in their
   relations, not in a catalogue of different pieces (`history/cascade/findings.md` L44: one
   role-field of the eight chair orientations of one shape plus one rule is a monotile encoding).
4. **Three separate achievements.** Existence, forced asymmetry, and the selection of a particular
   tiling are distinct obligations with distinct evidence; a design method must keep them apart.

## 1b. The framework's own statement of the phenomenon (verbatim source, for §1.3)

Foundations VI, cluster D "productive obstructions", Theorem G11 (`../six-birds-papers/
Tsiokos_2026_Six_Birds_Foundations_VI_A_Catalog_of_Dynamical_Structural_Laws.tex`, L2044–L2056;
Zenodo doi:10.5281/zenodo.22254289, preprint v1.0):

> Theorem (Local-Rule Global-Anti-Symmetry). Assume: [H-G11-hierarchy] every globally admissible
> C-configuration carries the declared hierarchy uniquely at every scale; the hierarchy is locally
> forced by the rules of C; and for every nonzero period vector p some scale k has forced marker or
> block structure that cannot be invariant under translation by p; [H-G11-nonempty] at least one
> global configuration satisfies all local rules of C. Then admissible configurations exist; for
> every nonzero p the hierarchy supplies a scale whose forced structure is incompatible with
> p-periodicity; because the forcing is local, the incompatibility is witnessed on a finite region
> R_p, yielding a per-period defect certificate; and therefore every admissible configuration is
> aperiodic.

Setting (L2024–L2033): C a finite local constraint system over configurations Z^d → A (a subshift
of finite type); "per-period defect certificate" = a finite region R_p on which the rules are
inconsistent with x(v+p) = x(v); "hierarchy certificate" = scales L_k → ∞, finite block types, locally
readable marker data, unique decomposition at every k. Provenance line (L2057): "RECOVERED STANDARD
in mechanism: the proof shape is Robinson's hierarchical forcing and the undecidability face is
Berger's theorem … SHARPENED as a typed record (per-period defect certificate, hierarchy
certificate)." Role reading (L2094–L2096): "G11 is P2 constraint gating, P4 hierarchy across forced
scales, and P1 descent obstruction per candidate period --- the productive obstruction is precisely
local-rule incompatibility with periodic descent." Calibration list (L2086–L2093, L2102–L2106):
Berger, Robinson, Penrose, "the hat (aperiodic monotile, reflections allowed) and the spectre
(chiral, translations and rotations only)". Lean substrate (footnote, L2067–L2074): theorem
`g11_global_anti_symmetry` via `admissible_configurations_exist` and `hierarchy_forces_aperiodic`
over `NonemptyAdmissible`, `Hierarchy`, `ForcedBreaksPeriod`
(`six-birds-foundations-vi/lean/SixBirdsFoundationsVI/Laws/G11GlobalAntiSymmetry.lean`, read
2026-09-08); the source notes the finiteness of R_p is prose, not mechanized. Non-claims the paper
must respect (L2603 ff.): "G11 … conditional on … per-period certificate data --- local
admissibility never globalizes for free, and G11 supplies no algorithm against Berger's
undecidability"; the quasicrystal-model boundary (a material is an instance only after a
local-rule model and hierarchy are supplied).

Instantiation for Q (the sentences the paper makes, ledger rows H11, T1, T8, T13; tiers at the
pinned commit d90313a717):

- *The finite local constraint system.* G11 is stated for configurations Z^d → A over a finite
  alphabet. Tilings of R³ by Q are not literally such configurations; the bridge is registration:
  every tiling by Q is, after one ambient isometry, a labelling of Z³ by the 168 registered cell
  labels obeying the 44-contact atlas (`registration_of_tiling`, T1n, A-T6.3), and conversely every registered baseline tiling with matching profiles is
  realized by a tiling of Q (the small-collar realization, R§8, `small_collar_realization_holds`, T1n). Call this labelled system
  C_44. The paper states G11's instantiation for C_44 and carries it to Q through these two
  statements, each at its tier; it does not claim a packaged theorem that C_44 and the tilings of
  Q are one object.
- *[H-G11-nonempty]* for C_44: a registered tiling exists (the substitution's baseline tiling,
  R§8–9), hence a tiling of Q (Theorem 1.2(1), `r44_einstein` first conjunct, T1n, unconditional).
- *[H-G11-hierarchy]* has three clauses. (i) Unique hierarchy at every scale: `carrier_hierarchy`
  and `carrier_hierarchy_unique`, with `geometric_hierarchy_canonical` and `geometric_hierarchy_unique`
  for arbitrary geometrically nested registered families (T1n; external review 2026-09-09 M2, ledger M9 closed). (ii) Locally forced by the rules: the level-1 parent
  of a cell is determined by its labelled first shell (Theorem 7.1: `parent_local_to_global` from
  the 33 shells, the 14/18 completions and the 28 conflicts, T1n, including the local-to-global assembly), and the coarsened
  tiling obeys the same atlas (`parent_atlas_eq_fine`, T1n), so the same finite rule determines
  the parent at every level from a neighbourhood whose radius grows with the level. This is local
  forcing in G11's sense (locally readable marker data at each scale); it is NOT local derivability
  from the unlabelled chair, which ruling R7 withdrew, and it rests on registration (T1n).
  (iii) A scale that breaks every nonzero p: our proof does not exhibit, for each p, a scale and a
  marker pattern; it proves Per(T) = {0} by the halving tower (a period p of T is a period p/2 of
  the coarsened registered tiling, `period_halving`, `all_periods_grid`; iterating, p/2^n ∈ Z³
  for all n, so p = 0, `no_period`; T1n for the tower and its application to Q; T1 for the final arithmetic implication `no_period`). G11's proof sketch is this mechanism (unique
  composition ⇒ a period would be invariant at every scale), but the paper states plainly that it
  reaches G11's conclusion by the tower and does not extract G11's per-period finite defect
  certificates R_p.
- *Conclusion.* Theorem 1.2(2)'s Per(T) = {0}. The symmetry bound |Sym(T)| ≤ 24 and homochirality
  are stronger than G11 asks and are stated separately.

## 2. The design test the reading yields

A candidate solid Q with a substitution structure passes the test when its own contact rule
survives coarsening: the language of legal contacts among decoded parents must lie inside the
language of legal contacts among the tiles themselves, so that the coarsened tiling is again a
legal tiling and a period of a tiling is a period of the coarsened tiling. Equality of the two
languages is the sufficient form that is checked; it is sufficient, not necessary, for the
stationary self-similar halving argument (a strictly smaller decoded language would also preserve
legality). When the decoded language is strictly larger, the parents obey a weaker rule and the
argument fails; whether a periodic parent tiling then exists is not a general theorem but must be
checked, and in the one case that arose (P4) it did: the decoded language was the complete
bare-chair language, every bare-chair tiling refined to a tiling of the candidate, and periods were
exactly preserved, so the candidate was periodic. P4 shows this for its own strictly larger
language only. The test is therefore a diagnostic and a sufficient condition for the halving
argument, not a necessary one and not a theorem about all candidates. In the framework's terms it is the sufficiency and composability gate (F7, F28):
admissibility must descend through the coarsening; the packets call this a structural
interpretation. (Foundations IV itself contains no tiling instance; that reading
of F7/F28 is the packets' own bridge, stated in their `SOURCE_AUDIT.md` files, and the paper
attributes it to the packets, not to the catalog; dossier `sixbirds_B_foundations_IV_laws.md` §4–§5.) In the community's terms it is exactly the self-similarity of the
atlas that makes period halving legitimate. The finite check is `parent_atlas_eq_fine` (T1n): the
halved parent atlas equals the fine atlas.

## 3. How the test produced R44 (facts, with packet evidence)

1. **The carrier and the marks that could not be geometrized** (repository cascade, steps 140–165;
   `LINEAGE.md` item 1; `history/cascade/findings.md` L40–L48). The seven-cube chair as a rep-8
   rep-tile; a single-marking local rule (R1+R2) admits the chair substitution and, by SAT, no
   periodic tiling up to L = 7; the cascade's own record calls the all-scale recursion an "honest
   gap", so this is a marked candidate with strong finite evidence, not a proved marked einstein.
   Attempts to realize the marks as notches fail; the verdict at the time was that the forcing rule
   is too complex for fixed covariant notches.
2. **Features on the panels; the first bare solid is a periodic control** (P3, 2026-09-06). 192
   square pyramids with signed heights on the 24 panels. The same connected 3-ball admits an
   all-scale aperiodic hierarchy and also a legal eight-copy periodic fine tiling whose known
   coarsening violates the solid's local geometry (P3 `README.md`). P3's own diagnosis: the failure
   is a preservation obligation, not a missing existence witness (P3 `SOURCE_AUDIT.md`, "SBT
   interpretation"), i.e. requirement 3 of §1 fails.
3. **Reverse descent: the decoded parent language is the wrong language** (P4). Unique first-parent
   grouping proved for that solid; the decoded parent space is the unconstrained bare-chair space,
   62 fine contacts decoding to 398 parent contacts (P4 `PROOFS.md` L106, L136); theorem: no bounded
   fixed-pose replacement or bounded local recoding of that fixed-frame hierarchy can be an einstein
   (P4 `README.md`). P4's gloss: Q-admissibility is not the same predicate as bare-chair
   admissibility after rescaling (P4 `SOURCE_AUDIT.md`).
4. **The move: change the child frames so that the parent language is the fine language** (P5).
   The central new finite identity: admitted fine contacts = admitted rescaled parent contacts = 44,
   against 62 → 398 before; the fixed-placement no-go is not contradicted because the native child
   frames are different (P5 `PROOFS.md`, "Claim and evidence status"). The 19 contact frames
   generate the full 24-element proper cubic group (`orientation_group_24`, T1n); the atlas equals
   its own rescaled parent atlas (`parent_atlas_eq_fine`, T1n). `LINEAGE.md`: this is the decisive
   move, "the admissibility gate (F7 / F28) that the earlier lossless decoder failed".
5. **Alignment** (P6): the written proof that every tiling, not only registered ones, is forced onto
   the lattice (the "geometric recognition theorem" the reading still requires), the companion
   census and the collision boxes.

## 4. What the paper will and will not say about the method

Will say (ledger rows H1–H13):
- H1 the reading of §1 in one paragraph, naming the framework once with its citation, and stating
  that in the community's terms it is recognizability, unique composition and period halving read
  as a design target;
- H2 the design test of §2 and its finite form `parent_atlas_eq_fine`;
- H3–H5 the three concrete steps (marked chair; 398 ≠ 62 periodic control; 44 = 44 with the
  24-element frame group), each a computed fact in a hash-chained packet, with the packet named;
- H6 what the method does not do: it proves neither existence (the substitution does) nor alignment
  (Part A does); existence, forced asymmetry and selection are three separate achievements;
- H7 provenance: the packets are hash-chained and replayed (`provenance/HASH_CHAIN.md`);
- H8 one open problem in §9: whether the same design test yields einsteins in other crystallographic
  settings or dimensions;
- H9 acknowledgement of the Six Birds corpus and of the automated reasoning agents, by role.

Will not say: that the einstein sits in the Clay-problem taxonomy of the framework's other papers
(the hiddenness, needle and self-dual-confinement papers do not mention tilings, and two of them
explicitly withhold the Clay-problem identification in their own text; dossier
`sixbirds_E_clay_taxonomy.md`); the phrase "productive obstruction" is used only as G11 uses it
(Foundations VI L2013–L2017, L2095–L2096), and any wider "productive obstruction to periodic
descent" formulation is presented as this paper's own reading; that the framework proves anything about Q; that the reading is new mathematics (its
ingredients are classical; Durand–Romashchenko–Shen's self-similar tile sets are the nearest
precedent for "unique N×N composition forces divisibility by N^k"); that the method guarantees
other einsteins; anything the packets do not record; nothing from the private thread.

Wording discipline the framework itself prescribes (dossier `sixbirds_D_nondescending_AOR_II.md`
§5, quoting the non-descending-objects paper): "This vocabulary alone does not certify any claim";
a claim accepted under an instrument "is an instrument-indexed claim, not an instrument-free truth
claim"; an audited descent "does not by itself license" literalizing the promoted object. The paper
therefore says, once, that the framework supplied a reading and a design test, that every
mathematical claim is certified by the proof and the Lean/replay record and not by the framework,
and it never presents G11 or any law as a step of the proof.

Owner rule (2026-09-08): the paper must not become a Six Birds paper; framework vocabulary is confined to §3.3 and used carefully; the abstract and §1.3 say the same things in the audience's language with one pointer to §3.3.

Audience fit: ≈ 800 words, placed as §3.3 "How the tile was found" after the substitution (the
hat's §2 position), concrete and numeric, opened by a labelling sentence ("This section records how
the solid was found; nothing in it is used in the proofs"). The community's referees accept a
discovery narrative (hat §2) and reject a framework pitch; the section therefore leads with the
three computed facts and names the framework once, with its citation.

## 5. Needed from the owner

- Confirmation of the self-DOIs of the Six Birds papers other than Foundations VI (taken from the
  first Zenodo DOI in each source; listed in `paper/review/BIB_UNVERIFIED.md`), and which versions
  to cite.
- Confirmation that the marked-chair cascade (steps 140–165) is credited as step 1 of the discovery,
  as `LINEAGE.md` does, and that the packets may be named in the paper as the record of steps 2–5.
- Whether Durand–Romashchenko–Shen should be cited for the composition argument (not in the corpus;
  to be fetched if so).
