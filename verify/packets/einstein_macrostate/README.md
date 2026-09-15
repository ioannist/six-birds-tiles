# R44 — a 3D Einstein proof submission

This batch contains one explicit rational polyhedral 3-ball and a proposed proof that all of its Euclidean tilings have finite symmetry groups. Rotations and reflections are permitted. **No independent external review or proof-assistant kernel verification is claimed.**

The computer-assisted registered theorem is:

- the solid tiles all of space;
- every registered tiling has a unique eight-copy parent partition;
- the rescaled parent contact atlas is exactly the original 44-contact atlas;
- iteration rules out every nonzero translation.

The new unrestricted geometric proof forces each small pyramidal feature to have a unique complete companion. Its finite collision certificate removes every noninteger feature-mate placement. Marker connectivity then forces global registration. These geometric lemmas are the critical review target, not an assumption quietly added to the final theorem.

## Replay

```bash
python src/replay.py
```

Requires only Python's standard library, with assertions enabled. No SAT solver, numerical library, network access, or Lean installation is needed. It runs the independent integer-matrix finite verifier and the exact actual-mesh angle audit.

## Main artifacts

- `PROOFS.md`: full proposed proof, including the non-face-to-face alignment argument and its scope.
- `REVIEW_PROMPT.md`: focused adversarial-review request.
- `SOURCE_AUDIT.md`: source/new-result separation and SBT grounding.
- `results/r44_solid.json`: exact rational vertex/triangle model and every native feature.
- `results/r44_solid.obj`: viewable mesh; rational coordinates in JSON are authoritative.
- `results/native_panels.csv`: compact human-readable 24-by-8 coefficient table.
- `results/candidate_certificate.json`: hierarchy, all 2,388 raw registered contacts, all 33 first shells, parent completions, and exact recurring parent atlas.
- `results/companion_collision_certificate.json`: 5,273 rejection witnesses; all 299,975 possible required-companion collisions are independently recomputed.
- `results/feature_alignment.json`: complete-feature mate census.
- `results/verification.json`, `results/edge_audit.json`, `results/replay.json`: actual checker outputs.
- `upstream/einstein_reverse_descent.zip`: unchanged preceding source packet.

Discovery scripts and their frame scan are included for provenance, but the theorem does not depend on trusting their assertions or on an exhaustive negative result over that scan. The independent checker reconstructs the chosen positive construction from integer matrices.

The proposed unrestricted claim should be treated as a proof submission pending adversarial review, not as an externally established result or a priority assertion.
