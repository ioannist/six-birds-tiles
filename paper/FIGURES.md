# FIGURES.md — figures and tables of the R44 paper

WRITING_PLAN.md step 7. Every number in a table is produced by a script from the certificates
or the Lean/replay outputs; every figure is rendered from `solid/r44_solid.json` and the
canonical child poses (`simulations/patches.py`). Nothing here is verification. Status codes:
EXISTS (in `figures/`), TODO (script to write under `paper/scripts/`), DATA (table built by a
script from `certificates/` / `verify/` outputs).

## Figures (in order of appearance; roles follow the hat/Spectre inventory, profile §2)

| # | Content | Role | Source | Status |
|---|---|---|---|---|
| 1.1 | Monochrome solid Q: carrier and feature centres unchanged, feature bases ×5 and heights ×80; matching panel 13 inset and signed sections | the object the theorem names, with explicitly exaggerated features | `figures/print-preview/build_preview.py` → `figure1-corrected.pdf`; per-feature and mesh read-back audits in the same directory | EXISTS |
| 1.2 | Proof roadmap, two flowcharts: existence (substitution → small-collar realization) and universality (features force companions → registration → unique parent → hierarchy → period halving), each box labelled with its section and tier | the hat's Figs 1.2/1.3 | `paper/tex/fig_roadmap.tex` (TikZ, hand-laid) | EXISTS |
| 2.1 | Oblique and plan views of the same panel 13: eight pyramids, signed coefficients, bases ×5 and heights ×80 (labelled) | the mechanism | `figures/print-preview/build_preview.py` → `figure3-corrected.pdf` | EXISTS |
| 2.2 | The seven-cube chair carrier P with its 24 exposed panels numbered, and the profile table's sign pattern as a diagram | definitions of panel/role/profile | `paper/scripts/carrier_panels.py` → `generated/fig_carrier_panels.tex` (six axis views, panel numbers, signed magnitudes at the marks) | EXISTS |
| 2.3 | Schematic feature geometry (exaggerated height): a pyramid of height j/10000, base half-width 1/100, its deviation angles, and the interior cone with slope bound L = 3/25 | A-L3.1 / A-L4.1 | `paper/tex/fig_feature_geometry.tex` (TikZ schematic, exact numbers printed) | EXISTS |
| 3.1 | The eight-child dissection: eight rotated copies forming 2P | the substitution rule (Spectre Fig 2.1 role) | `render_r44.py --only cluster` → `r44_parent_cluster.png` | EXISTS |
| 3.2 | Two refinements: 64 copies coloured by parent | supertile picture (hat Fig 2.7 role) | `render_r44.py --only patch` → `r44_patch64.png` | EXISTS |
| 3.3 | The 44-contact atlas as a picture: root chair with the 44 legal neighbour poses, or a table of (frame, offset) pairs | the finite object the whole proof turns on | `paper/scripts/atlas_44.py` → `generated/atlas_44_table.tex` (the 44 (frame, offset) pairs as a table) | EXISTS |
| 4.1 | Companion argument schematic: a feature's edge, its complementary partner, the sector budget at a generic edge point | A-L3.2 / A-T4.2 | `paper/tex/fig_companion_sectors.tex` (TikZ schematic) | EXISTS |
| 4.2 | Schematic of the retained-core overlap estimate (Proposition 5.2); not a selected certificate witness | A-L5.1 / A-FS5.2 | `paper/tex/fig_collision_box.tex` (TikZ schematic of one collision box; the certificate stores the boxes) | EXISTS |
| 6.1 | The 33 first shells as atlas indices, their proposed parent types and central-completion outcomes (table) | R§7 | `paper/scripts/first_shells.py` → `generated/first_shells_table.tex` (the 33 shells as atlas indices, parent, completion verdict) | EXISTS |
| 6.2 | The 0 ≤ z < 1 unit-cell slice of the 64-chair patch 4P: colours identify level-1 parents, bold lines the level-1 and level-2 boundaries | C3 `carrier_hierarchy` | `paper/scripts/nesting_slice.py` → `generated/fig_nesting_slice.tex` (slice of the 64-chair patch, level-1/2 outlines, from the child poses) | EXISTS |
| 8.1 | The modular-coincidence address and the all-address distributions of label-set sizes at depths 1–3 (ledger L8) | C3(c) | `paper/scripts/coincidence_tree.py` → `generated/fig_coincidence.tex` (from the coincidence script's JSON) | EXISTS |
| A.1 | Viewer screenshot with the feature inspector | reader engagement (hat L96) | `viewer/index.html` | DROPPED (no browser in the build environment; the viewer is described in Appendix A) |

## Tables (all DATA, generated)

| # | Content | Script / source |
|---|---|---|
| 1 | The finite theorems: name, statement in words, method (decide / native_decide), the number it certifies | `lean/R44/AXIOMS.md` decision-method ledger + `Theorems.lean` docstrings → `paper/scripts/finite_theorems_table.py` |
| 2 | The censuses: 2,388 → 44; 33 shells; 14/18; 28 conflicts; 697 → 116 → 44; 6,862 → 5,317 → 44; 299,975 boxes; 168 labels, N=3, M=3 | `verify/replay_report.json` (scratch run) + `verify/substitution_modular_coincidence.py` output → `paper/scripts/census_table.py` |
| 3 | The 19 written lemmas that formed the `Hypotheses` record (empty at the pin): former field, written lemma label, Lean theorem, tier by its axiom line, proof note | `lean/R44/HYPOTHESES.md` (Discharged), `lean/R44/PAPER_UPDATES.md` §2, `lean/R44/build_axioms.log` (pinned commit) → `paper/scripts/hypotheses_table.py` |
| 4 | Axiom lines: `r44_einstein` and the finite theorems | `lean/R44/build_axioms.log` (pinned commit; re-run at freeze) → `paper/scripts/axioms_table.py` |
| 5 | Mesh facts: V, E, F, χ, volume, dihedral classes | `solid/r44_solid.json` (+ `boundary_sphere`, `mesh_angle_audit`, `verify/boundary_sphere.py` as the checks) → `paper/scripts/mesh_table.py` |
| 6 | Input hashes and tool versions | sha256 of the inputs, tool versions (APPENDIX_DATA.md) → `paper/scripts/appendix_data_table.py` |
| 7 | The parameter family conditions (R§11), with their values at the explicit member | `proof/PROOFS_registered.md` §11 → `paper/scripts/parameter_family_table.py` |

Every generator writes `paper/tex/generated/<name>.tex` (a `tabular` body), which the section file
`\input`s; the grey one-row stub stays in place until the generator has run.

## Rules

- Colours are annotation only (README wording); every caption says so where colour appears.
- Feature-width and height exaggerations are labelled on the images and in their captions;
  feature centres, polarities and relative heights are preserved. The paper's Figures 1 and 3
  use bases ×5 and heights ×80, with all 192 source features checked individually.
- Case-analysis figures (hat §5 style) are not planned: the census is a table and a replay,
  not a figure.
