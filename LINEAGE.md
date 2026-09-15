# LINEAGE.md — how R44 came to be

## In this repository (the cascade, now under history/cascade/)

The construction cascade ran 350 numbered steps from 2026-06 to 2026-09-06
(`history/cascade/manager_log.md`, `cascade_map.md`, `findings.md`). Four
candidate lineages matter for the paper:

1. **Marked chair rep-tile, steps 140–171 — the ancestor of R44.**
   Step 140 introduces the seven-cube chair as a rep-8 rep-tile. Steps 149–152
   prove a single-marking local rule (R1+R2) that forces the chair
   substitution: a *marked* strongly aperiodic 3D monotile
   (`history/cascade/findings.md`, "monotile theorem"). Steps 153–165 try to
   geometrize those marks into a bare solid (interlocking, corner-star CAD,
   stencil bakes, edge interlock) and fail; the verdict at the time
   (`history/superseded_docs/EINSTEIN_VERDICT.md`) is that the chair's forcing
   rule is too complex to realize as fixed covariant notches.
2. **Dense W21/Fletcher determinant-skin solid Qψ, steps 172+**
   (`history/superseded_docs/PROOF_CHAIN_V8.md`, `VERIFICATION_STATUS_V5.md`,
   `history/lean_qpsi/`). Self-corrected as an overclaim in the V9 external
   request: two decoupled layers, dense bareization never done.
3. **AKN / ⟨ABCK⟩ icosahedral AWSS route** (`history/external_dialogue/`,
   `history/superseded_docs/AWSS_LAW.md`, `COADEQUACY_PROOF.md`). Structural
   dead end: disjoint-packing number 2 versus required 5. Closed.
4. **Stepped-hat 70-mask family, steps 325–350** (`history/GOAL_checkpoint350.md`,
   `history/cascade/PAUSED_CHECKPOINT_2026-09-06.md`). 11 periodic, 57 excluded
   in the grid class, 0145 and 1267 open at the pause. Closed as history: the
   external packet 1 shows 1267 periodic; 0145 is not pursued.

The 2D calibration (`calibration_2d/`, same day as the pause) reconstructs the
published hat with explicit proof dependencies and a Lean-checked abstract
period-exclusion tower; it is the paper's warm-up and the template for the
Lean skeleton.

## Outside this repository (the six packets, provenance/packets/)

An external reasoning thread took over from the checkpoint-350 snapshot
(`provenance/six-birds-tiles_checkpoint350.zip`) and produced six packets,
each embedding or naming the previous by hash (`provenance/HASH_CHAIN.md`):

| # | Packet | What changed |
|---|---|---|
| 1 | einstein_takeover_handoff | signed cap synthesis on the stepped-hat masks; 1267 shown periodic (4-copy cell); 0145 left open |
| 2 | einstein_next_batch | LRAT-checked closure of the pending 1267 refutation; 8-copy sidewall control; collared-repair classification. Controls only |
| 3 | einstein_recursive_interface | **pivot back to the chair** (cites steps 152/153/155): 192 square-pyramid features on the 24 panels, signed heights; a solid that admits an all-scale aperiodic hierarchy but also an 8-copy periodic tiling |
| 4 | einstein_reverse_descent | unique parent partition of that solid; decoded parent language = all bare-chair tilings (62 fine → 398 parent contacts); no bounded recoding of *that* fixed-frame hierarchy can be an Einstein |
| 5 | einstein_r44_proof_submission | **the new frame table**: proper-rotation child poses generating the full 24-element cubic group; contact closure 21→30; 44-contact atlas that equals its own rescaled parent atlas (697→116→44); solid R44; registered theorem finite-certified; first unrestricted-alignment argument |
| 6 | r44_unrestricted_alignment | closed written alignment proof for the unchanged R44 (finite disjoint closed cover on the connected feature graph; equal-length rigidity; explicit collision boxes); mesh-derived re-verification; mutation controls |

The decisive move between 4 and 5 is the change of child frames. With the old
fixed frames the decoded parent obeyed a weaker rule (398 contacts); with the
new proper-rotation frames the decoded parent obeys exactly the same 44-contact
rule, which is what makes period halving legitimate (R§8, R§10). In the SBT
vocabulary used throughout the cascade this is the admissibility gate (F7 /
F28) that the earlier lossless decoder failed; see `proof/SOURCE_AUDIT_registered.md`.

## What the repo contributed, stated plainly

The chair carrier, the marked-chair forcing theorem, the "one shape ≠ one
role" reframing, the SAT/LRAT verification discipline, and the checkpoint the
external thread started from. The bare geometrization, the frame table, the
44-atlas self-similarity and the unrestricted alignment proof are the external
packets' work, replayed and hash-verified here.
