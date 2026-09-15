# R44: closed unrestricted-alignment proof and mesh-derived audit

This packet gives a complete written unrestricted-alignment proof for the **unchanged** R44 solid from the preceding proof-submission archive. It is not a new solid or a restricted-grid restatement.

The proof first forces one full pyramid companion in an arbitrary tiling, then excludes every nonintegral companion, then proves that a single feature-connected component covers physical space. Registered aperiodicity is used only afterwards as a corollary.

**Verification status:** the finite gates have been replayed by a new mesh-derived standard-library verifier. Continuous geometric lemmas have written proofs, not proof-assistant proofs. No independent external review, publication acceptance, or priority claim is asserted.

## Read

- `ALIGNMENT_PROOF.md`: full mathematical proof, including exceptional points, closed-set nonbranching, rigid feature equality, and global coverage.
- `SOURCE_AUDIT.md`: unchanged-input hashes and source/new-work boundary.
- `CLAIM_LEDGER.md`: exact status of each obligation.
- `results/alignment_verification.json`: new mesh-derived audit.
- `results/core_box_replay.json`: independent integer-only replay of all physical collision boxes.
- `results/collision_core_witnesses.jsonl.gz`: an explicit retained-core overlap box for every one of the 299,975 excluded companion options.
- `results/mutation_controls.json`: deliberately altered geometry/certificates rejected by the new checker.
- `upstream/einstein_r44_proof_submission.zip`: byte-preserved source archive, including the registered existence/recognition proof and its original checkers.

## Replay

From this directory:

```bash
python src/replay.py
```

Only Python's standard library is needed. The script runs the new mesh-derived alignment checker, the separate integer physical-overlap checker, and the original two checkers in a temporary extraction of the source archive. The fresh run's output is written to `results/replay.json`.

The checker extracts all 192 features from the actual mesh triangles before comparing the annotations. It reconstructs all 6,862 complete-feature mates over all 48 cubic orientations, and it tests every possible isolated companion of every indicated feature. It does not use the earlier flat-panel filter as a proof premise or prune the companion lists using previously rejected pairs.

Optional mutation controls:

```bash
python src/test_mutations.py
```

The OBJ inside the source archive is a viewing aid. The rational JSON is authoritative. No claim is made about tolerance to printing errors or noisy angle measurements.
