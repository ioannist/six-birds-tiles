# Source audit and provenance

## Requested basis

The user's request was to finish the unrestricted-alignment proof of the supplied R44 candidate. The primary input is the attached `einstein_r44_proof_submission.zip`, not an online description or an inferred reconstruction of an absent file. It was present and extracted in this session. Its `PROOFS.md`, `CLAIM_LEDGER.md`, `REVIEW_PROMPT.md`, actual rational solid, finite certificates, and both original checkers were inspected.

The source's Sections 2–5 contain the proposed unrestricted argument. Its main self-reported gap was review/formalization status of continuous reasoning, not a missing enumerated pose class. The original checks were actually replayed successfully in this session.

## Unchanged exact inputs

- `input/r44_solid.json`: SHA256 `f320d7a0c2d784a3eb29f001dc035808f67591d9ea8d3dd45949e66442f0ed55`.
- `input/companion_collision_certificate.json`: SHA256 `36e89e2fe81f4788e7edea2a68fef013557e5b73f5a16ac76348fe241b068b08`.
- `input/candidate_certificate.json`: SHA256 `44e9b3f6048497de02d1be72d0c80ddc94aaaf235382138c7468ffdbc5de5ff2`.

The entire unchanged upstream archive is included. `MANIFEST.json` records its hash and those of the new immutable documents, code, and explicit overlap certificate.

## New work in this packet

- A self-contained alignment proof, replacing the informal no-switch/edge-continuation passages with a finite disjoint closed-cover argument and an equal-total-length argument.
- A weaker sufficient cone condition, 8L^2<1, explicitly proved and checked; the source's stronger 63L^2<1 also remains true.
- Explicit treatment of the finite exceptional set on an arbitrary root edge, including non-face-to-face contacts.
- A complete physical-cover proof for the feature component, with an explicit global tube homeomorphism and exclusion of extra components.
- `src/verify_alignment.py`: a separately written checker using signed images of input basis vectors. It imports no upstream code. It extracts square-pyramid features from the connected sloping-face components of the actual triangular mesh, reconstructs the mate inventory, and checks every exclusion quantifier and positive-volume core overlap.
- `src/replay_core_boxes.py`: another small checker, using integer coordinates in units of 1/400, to verify every exported physical collision box. It does not establish mate-list completeness; that is the preceding checker's separate obligation.
- Mutation controls and clean-bundle replay.

The new checker reuses the exact geometry and supplied witness choices. Algorithmic separation does not mean external human review, proof-assistant verification, or independently discovered input data. The declared input/output boundaries matter.

## Source claims retained rather than expanded

The registered unique-parent theorem and 44-to-44 coarsening rule are retained from the source packet. Its checkers have been replayed, and their mathematical role is stated in Section 7 of `ALIGNMENT_PROOF.md`. The present alignment theorem does not assume either theorem, so applying them afterwards is not circular.

No changes were made to the native solid, its feature heights, its frame system, or its certificate atlas. No new periodic search is used. No 3D-printing tolerance theorem is inferred from exact geometric rigidity.

## External context

A primary-source web search on polyhedral tiling alignment and aperiodic monotiles was made during this work. It returned, among others, Smith–Myers–Kaplan–Goodman-Strauss, *An aperiodic monotile*, arXiv:2303.10798v3. No outside paper is used as a premise proving R44 alignment, its parent grammar, or its novelty. The alignment reasoning is given in full from the supplied geometry.

The earlier SBT corpus distinguishes exact interface sufficiency from scope-complete geometric admissibility. Here no SBT axiom is invoked to promote a grid theorem into a Euclidean theorem: the missing geometric carrier reduction is proved explicitly. No new SBT/Lean mechanization is claimed.
