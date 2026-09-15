# 2D calibration — recovery checkpoint

Updated 2026-09-06. **2D controlled reconstruction complete:** see LANDING.md
and SELF_REVIEW.md. Authorized target: CHARTER.md. Sequential multi-round work;
new SBT theorems/extensions are explicitly permitted. The 3D step299 solid
and its remaining staggered cases are deferred.

| Round | Result | Evidence and scope |
| --- | --- | --- |
| R001 chair | Exact subdivision succeeds; bare Einstein claim fails | Four chairs cover twice the chair; two cover a 3-by-2 rectangle, giving an explicit periodic plane tiling. Separate verifier PASS. |
| R002 frozen maps | Boundary-only repair impossible with those exact maps | Hausdorff contraction fixes the compact support uniquely. Exact map/cover checks PASS; theorem in RESULT.md. Carrier-local exclusion. |
| R003 hat reconstruction | Exact geometry and local recognition replay PASS | 58 touching placements, four trap one-kite holes; 54 remain. Author search regenerated 2,380 two-coronas and 188 surroundable ones. Separate declarative matcher checks 1,391 roles and 516 intercluster conditions; same patch set as supplied reference. Alignment and enumeration completeness remain established paper imports. |
| R004 varying geometry | Derived tower endpoint proved | Coherent translation-covariant coarsening plus unbounded inballs excludes every nonzero period. Abstract Lean theorem builds; physical geometry is a separate input. |
| R005 exact hierarchy | Finite patch and all-scale macro growth checks PASS | Rational port of author grammar; 7,921-hat H patch has no overlap and a covered disk radius >136. Symbolic derivation gives edge-vector recurrence and inball lower bound (13/5)^n/100 for all four macroshapes. Infinite decoration compatibility/recognition use precise paper imports. |
| R006 finite ambiguity | Derived recognition extension proved | A finite equivariant set of global coarse layouts suffices when inradius divided by its cardinality is unbounded. Complete periodic-square offset actions and fixed-thickness controls PASS. Written proof, not Lean-formalized. |

Known-reference opening occurred **after** the two chair rounds and is recorded
in rounds/REFERENCE_OPENING.md. This is controlled reconstruction, not an
independent rediscovery of the hat. Source versions/hashes and BSD licence are
in sources/. The local hatviz copies from old step115 match the current author
commit exactly; the pinned snapshot is 4bb9d01999e4e84accc2a78d0fa279ef20b47263.

The target implication is assembled in LANDING.md and passed a distinct
mathematical self-review. Exact source bridges remain imported: alignment,
atlas completeness, all-level recognition and infinite decoration compatibility.
This is a completed known-example calibration, not a new monotile discovery or
a full Lean formalization. No finite search is treated as a global proof.

All useful results, controls and construction consequences are collected in
LESSONS_FOR_3D.md. Next concrete 3D witness: extruded hat layers retain the unit
vertical period; construct a geometric coupling that sees that direction while
preserving existence. This next design is specified, not yet implemented here.

Replay: python3 calibration_2d/replay.py from the repository root. Add
--enumerate to repeat the expensive complete 2,380-case source enumeration;
without it the saved enumeration is still checked against the reference set.
verification_receipt.json records the completed-run artifacts and hashes.
hat.svg and hat_patch.svg/png illustrate the returned shape and a 1,156-hat
patch. The drawings use rounded display coordinates; the JSON data is exact.

Completed processes: author enumeration, finite construction, symbolic growth.
No research process remains running at this checkpoint.
