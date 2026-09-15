# Distinct mathematical self-review — 2026-09-06

Verdict: **the charter's controlled reconstruction of a known 2D Einstein is
complete, with the established imports explicitly retained in LANDING.md.**
This is not an independently discovered shape, an import-free reconstruction of
every source lemma, a complete Lean formalization, or a new 3D construction.
There was no independent reviewing agent or external referee.

## Adversarial target audit

| Possible failure | Check and disposition |
| --- | --- |
| Only one selected tiling is nonperiodic | The arbitrary input T enters through universal A.6, 4.1 and 5.1; the endpoint excludes each nonzero vector for every T. |
| A vacuous empty tiling space | Theorem 2.1 provides whole-plane existence for the exact returned polygon. The finite implementation is supporting evidence, not a replacement for this import. |
| Extra coloured rules were imposed on the bare tile | The role labels and edge laws are recognized outputs of actual geometric neighbours. The target admits all congruent copies, including reflections. |
| A finite grid search misses continuous placements | A.6 is explicitly imported in the universal direction; the finite search does not stand in for it. |
| Only doubly periodic tilings are excluded | The inball contradiction uses a single arbitrary vector, so singly periodic tilings are also excluded. |
| Large counts or long thin patches are mistaken for growth in every direction | R005 measures covered disks and separately proves uniform macro inballs. R006 includes a fixed-thickness stack control. |
| The changing shapes invalidate a fixed substitution endpoint | R004 allows a dependent family of geometric levels. No stationary endomorphism is assumed. |
| Different boundary representations are silently identified | The source's bisected decorated macrotiles and hatviz convex outlines are distinguished. Boundary compatibility and the recognition representation's growth remain explicit source inputs. |
| Edge labels alone justify iteration | The imported Section 5 argument also checks vertex angle closure. This is retained in the proof graph. |
| A replay is presented as independent enumeration completeness | The search is the author's brute-force implementation, replayed locally. Separate integer contact geometry and rule arithmetic are distinguished from the source completeness proof. |
| A local no-go is promoted to a global theorem | R002 fixes the contracting maps; it does not exclude grammar/map changes. The 3D aligned-fan exclusions remain scoped and deferred. |
| A new theorem hides the desired answer in an axiom | R004 proves an implication from real coarsening/separation inputs; R006 proves a finite-orbit argument. Neither constructs a 3D solid. |
| Finite ambiguity means finitely many local choices | R006 explicitly requires a finite set of entire global coarse tilings, and controls its growth. The periodic square example shows why unbounded ambiguity matters. |
| Lean checked the complete physical theorem | It checked only the exported abstract period-transport theorem. Geometry, existence and recognition were not Lean-formalized. |

## Corrections and retained limitations

- R005 initially checked absolute grid phase, which differs between independently
  positioned macros. The corrected check normalizes by the first hat and verifies
  all relative placements exactly. The initial assertion failure and correction
  are recorded in its RESULT.md.
- The four two-hat holes were initially classified by Euler characteristic.
  A separate complement-cell calculation now proves their one-kite sizes and
  checks each hole boundary abuts occupied cells, excluding an artificial box
  boundary artefact.
- Reconstructed and reference patch files differ in ordering, so byte hashes
  differ. Equality is checked on the complete sets of sorted placements/levels,
  including uniqueness and the count 188.
- Paperclip's earlier text file is a truncated overview. Source-reading claims
  use the subsequently downloaded full v3 PDF/text and the relevant full sections.
- The straight macro growth computation checks a full symbolic parameter
  interval with positive rational Bernstein coefficients. Its proof is not a
  fit to the five numerical examples. The interval's invariance and the exact
  recurrence give the induction for every n.

The geometric proof chain closes with established imports; it has no remaining
unproved 2D construction input under that declared standard. Full independent
reproof or full mechanization would be a larger, different task. The construction
and universal-recognition inputs needed in 3D remain genuinely unconstructed.
