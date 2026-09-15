# APPENDIX_DATA.md — verification appendix material, captured from real runs

WRITING_PLAN.md step 8. Everything below was produced in this session from the repository at
the state recorded in §1, except the Lean gate figures, which are read from the mechanization
lane's committed gate log (§5) because a Cody build was in flight and a second `lake build`
must not run concurrently. Fields marked PENDING are filled at the step-8 gate.

## 1. Repository state

- State: pinned commit `d90313a717` (2026-09-10; re-pinned once from dd2735d9bd, DECISIONS.md Q-K; `Hypotheses` empty, `r44_einstein` unconditional). The hashes identify the canonical inputs at this baseline. Historical outputs retain their stated dates; the clean-clone replay at d90313a717 is recorded in REPLAY_FROM_PAPER.md and replay_from_paper_transcript_2026-09-10.txt.
- Canonical inputs (sha256, computed 2026-09-08):

| file | sha256 |
|---|---|
| `solid/r44_solid.json` | `f320d7a0c2d784a3eb29f001dc035808f67591d9ea8d3dd45949e66442f0ed55` |
| `certificates/candidate_certificate.json` | `44e9b3f6048497de02d1be72d0c80ddc94aaaf235382138c7468ffdbc5de5ff2` |
| `certificates/companion_collision_certificate.json` | `36e89e2fe81f4788e7edea2a68fef013557e5b73f5a16ac76348fe241b068b08` |
| `certificates/collision_core_witnesses.jsonl.gz` | `ae64a5283400c61e15f4a8758d949f3ad8428645cb3691e0b5cdb539161f8a45` |
| `solid/native_panels.csv` | `b9eec9fd834abba4149bbf021026723499c4bb9e20553ebfab691c9ed3a9ed2d` |

## 2. The one-minute replay (T2), exact command lines

```
python3 verify/replay.py
```
Plain `python3` (no `-O`), standard library only, no network. It asserts the sha256 of the
canonical inputs, copies the two proof packets to a temporary directory so their shipped
receipts are never overwritten, and writes `verify/replay_report.json`.

Run 2026-09-08 on a scratch copy of `verify/`, `solid/`, `certificates/` (so the tracked
report in the repository was not touched): **PASS, 27.2 s wall** (`real 0m27.199s`,
`user 0m26.789s`), on the same host that runs the Lean builds. Report sha256
`c6cca6f7e8c4bc86e949a88bde0bfbccb2ab670a24915ca1a3005ddbe4ea623d`.

Step outputs (verbatim tails from the report):

- `boundary_sphere: PASS (edges=two, triangle_graph=connected, vertex_links=cycles, V=2138, E=6408, F=4272, chi=2)`
- `tube_formula_controls: PASS (cases=4800, inverse-after-forward=4800, forward-after-inverse=4800, hypograph=4800, two-owner=4800)`
- `substitution_modular_coincidence`: `labels 168, column_sum 8, covered_cells_per_frame 56, least_primitive_exponent_N 3 (reachability min/max by power: 1:[7,8], 2:[49,50], 3:[168,168]), least_coincidence_depth_M 3, coincidence_address_a (0,0,2), coincidence_path (0,0,0),(0,0,1),(0,0,0), coincidence_label_i 78 = (frame 11: permutation (1,0,2), signs (1,1,-1); cell (0,0,1)), coincidence_label_set_sizes` as (size of the possible-label set, number of addresses with that size): depth 1: 8 addresses each with 42 possible labels; depth 2: 48 addresses with 6, 16 with 24; depth 3: 336 addresses with a single label, 160 with 6, 16 with 24 (336 + 160 + 16 = 512 = 8³). The tracked set starts as all 168 labels at the root (`states = [(ORIGIN, frozenset(range(168)))]`), so the coincidence is over all labels.
- packet `einstein_macrostate` (registered theorem, the first implementation): `verify.py` PASS 6.39 s, `edge_audit.py` PASS 0.37 s; `external_dependencies: []`.
- packet `r44_unrestricted_alignment` (second implementation and the alignment census): `verify_alignment.py` PASS 10.49 s, `replay_core_boxes.py` PASS 2.62 s, plus the unchanged upstream replay.

Also in the README's one-minute list (to be run and recorded at the gate):
```
(cd lean/R44 && python3 gen/extract.py --check)      # generated Lean inputs match canonical data
python3 -m unittest discover simulations/tests       # ~3 s
cd verify/packets/r44_unrestricted_alignment && python3 src/test_mutations.py   # six corrupted inputs rejected
```
Run 2026-09-08: `gen/extract.py --check` → `generated literals and SHA256 manifest: PASS`
(0.2 s, in the repository, read-only). `unittest discover simulations/tests` → `OK` (3.1 s, on
the scratch copy). `test_mutations.py` → 6 of 6 corrupted inputs rejected
(missing_triangle, reversed_triangle, changed_geometric_apex, missing_rejection_witness,
wrong_companion_quantifier, missing_registered_contact; e.g. the last fails with
"ValueError: survivors not identical to registered 44 atlas"); 15.7 s; scope line: "Checks
selected malformed inputs are rejected. Does not validate the continuous proof." (on the
scratch copy).

## 3. Exact arithmetic

Every certificate is integer or rational data (`Fraction` strings); the only decimal
literals in `certificates/*.json` are two `"seconds"` timing fields. All checkers use Python
`int` and `fractions.Fraction`; the only `float(...)` is the OBJ export for rendering
(`verify/packets/einstein_macrostate/src/build_solid.py:64`). Collision boxes are in integer
units of 1/400 (side ≥ 42/400 = 21/200). Lean data are `Int`/`Rat` literals decided by
`decide` / `native_decide`. (DECISIONS.md Q-D.)

## 4. Lean toolchain

- Lean `leanprover/lean4:v4.31.0` (`lean/R44/lean-toolchain`).
- Mathlib commit `fabf563a7c95` (`lean/R44/lake-manifest.json`), with batteries `fa08db58b30e`,
  aesop `e3cb2f741431`, Qq `f46324995fca`, proofwidgets `24b0d9dc081c`, importGraph
  `5c7542ed018c`, LeanSearchClient `c5d5b8fe6e51`, plausible `63045536fe95`, Cli `92564e5770e4`.
- Build cap `-j 4` in the lakefile; `.lake/packages` pre-seeded (7 GB); never `lake clean`.

## 5. Lean gate (from the committed gate log; a fresh run is PENDING until the lane's build
   finishes)

- `lean/R44/build_axioms.log` at the pinned commit (169 declarations with an axiom line). First lines:
  `R44.children_partition_2P` depends on no axioms; `R44.contact_closure_30` on its own
  `native_decide` hook only; `R44.profile_canonical` on `propext` + its hook; `R44.atlas_44` on
  `propext, Classical.choice, Quot.sound` + its hook; `R44.first_shells_33` on `propext` + hook.
- `r44_einstein` line, verbatim (from the committed log at d90313a717; cited by declaration name; no `sorryAx` anywhere in the core block):

  `'R44.r44_einstein' depends on axioms: [propext, Classical.choice, Quot.sound, R44.atlas_44._native.native_decide.ax_1_1, R44.central_completion._native.native_decide.ax_1_1, R44.contact_closure_30._native.native_decide.ax_1_1, R44.first_shells_33._native.native_decide.ax_1_1, R44.hierarchy_cell_controls._native.native_decide.ax_1_1, R44.mate_records_roles_nonempty._native.native_decide.ax_1_1, R44.mates_census._native.native_decide.ax_1_1, R44.mesh_angle_audit._native.native_decide.ax_1_1, R44.nested_substitution_controls._native.native_decide.ax_1_1, R44.orientation_group_24._native.native_decide.ax_1_1, R44.parent_atlas_eq_fine._native.native_decide.ax_1_1, R44.parent_conflicts_28._native.native_decide.ax_1_1, R44.profile_canonical._native.native_decide.ax_1_1, R44.registered_shell_cell_controls._native.native_decide.ax_1_1, R44.solid_mesh_exact._native.native_decide.ax_1_1, R44.transported_role_geometry._native.native_decide.ax_1_1, R44.DischargeCarrierStrata.carrier_coordinate_states_table._native.native_decide.ax_1_1, R44.DischargeMeshTrace.native_mesh_incidence_trace._native.native_decide.ax_1_1, R44.DischargeVertexData.carrier_vertex_lookup._native.native_decide.ax_1_1, R44.DischargeVertexData.feature_index_bounds._native.native_decide.ax_1_1, R44.DischargeVertexData.feature_vertex_lookup._native.native_decide.ax_1_1]` (21 named hooks)

  `tiling_homochiral` and `carrier_hierarchy` (cited by declaration name) depend on the same kind of set: standard axioms plus named `native_decide` hooks.
- Discharge library: none at the pin. `R44/Discharge/` holds no module, `sorryAx` occurs nowhere in the log, and controls.sh reports `admissions=0` (the three admissions recorded at dd2735d9bd are admission-free theorems in `Proved/`).
- `bash lean/R44/scripts/controls.sh` (positive build first, then must-fail files with checked
  diagnostics, scope regressions, admission count): PENDING transcript, build time, peak RSS
  (`/usr/bin/time -v`), to be run detached when no other build is running.

## 6. Two independent implementations (the disclosure sentence's evidence)

- Implementation 1: `verify/packets/einstein_macrostate/src/` (the registered theorem's
  checkers, written first).
- Implementation 2: `verify/packets/r44_unrestricted_alignment/src/` (derives the features from
  the actual mesh, recomputes the census and the collision boxes independently;
  `proof/CLAIM_LEDGER_alignment.md`: "New independent implementation derives features from
  actual mesh").
- Both are run unchanged by `verify/replay.py`; the Lean theorems are a third, kernel-checked
  derivation of the same finite facts from the same canonical JSON (`gen/extract.py --check`
  ties the generated Lean literals to the JSON).
