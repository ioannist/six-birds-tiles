# Chair44 (R44) simulations and inspection tools

Everything cited here except rendering uses Python 3's standard library. These
programs make the finite R44 data visible and reproduce selected T2 checks. They
do not prove the continuous T3 lemmas, the unrestricted-alignment theorem, the
all-level induction, or universal aperiodicity. The canonical verification
entrypoint remains `python3 verify/replay.py`; the trust ledger is in the root
`README.md` and `THEOREM.md`.

## Patch generation

Run from the repository root:

```sh
python3 simulations/patches.py
```

This writes `simulations/generated/sigma_0.json` through `sigma_3.json` and
physical Q-copy OBJ/MTL files through depth 2. At refinement depth `d`, there
are `8**d` Q-copies and `7*8**d` disjoint baseline unit cells:

| depth | Q-copies | baseline unit cells |
|---:|---:|---:|
| 0 | 1 | 7 |
| 1 | 8 | 56 |
| 2 | 64 | 448 |
| 3 | 512 | 3,584 |

For every patch, `patches.py` checks exact integer-cell disjointness and checks
every face-adjacent tile pair against the canonical 44-contact atlas. It also
checks the same-frame two-refinement grandchild relation.

There are two indices worth distinguishing. Section 9 defines the literally
nested sequence

```text
A_n = sigma_(2n)(P) - c_n (1,1,1),   c_n = 2(4^n-1)/3.
```

Thus its Q-copy counts are `1, 64, 4,096, 262,144`, while the packet's
`7, 56, 448, 3,584` figures are baseline-cell counts at consecutive refinement
depths. The default run checks every section-9 nesting pair available through
depth 3. To materialize the literal sequence separately, use, for example:

```sh
python3 simulations/patches.py --max-depth 2 --obj-through -1 --proof-max-level 2
```

`--proof-max-level 3` is supported but intentionally large. Proof-sequence OBJ
export is disabled unless `--proof-obj-through` is supplied.

Each pose has the certificate's exact form
`[[permutation, signs], integer_translation]`. OBJ files use the authoritative
mesh in `solid/r44_solid.json`; no triangle decimation or geometric inference is
performed. The accompanying MTL colors protruding features red, recessed
features blue, and baseline faces gray.

## Parent recognition

```sh
python3 simulations/parents.py simulations/generated/sigma_2.json
```

The recognizer uses the certified 22-cell first shell, 33 shell arrangements
and unique role table from `candidate_certificate.json`. It prints recovered
parent frames for tiles whose complete shell is present. Tiles whose shell
crosses the finite patch boundary are explicitly `undetermined`; the program
does not infer their parent from construction order. Generated pose files carry
construction-parent data only as a comparison oracle, and every independently
determined parent must agree with it.

## Twelve-height family

With no positional heights, the exact default `c_j=j` is rebuilt and compared
byte-for-byte with the canonical solid:

```sh
python3 simulations/family.py
python3 simulations/family.py 1 2 3 4 5 6 7 8 9 10 11 25/2
```

Inputs are exact rationals (integer, fraction, or finite decimal syntax). The
four conditions in `PROOFS_registered.md` section 11 are checked without
floating point. An accepted member is emitted in the same JSON schema, with all
192 profile entries and mesh apex coordinates updated. A repeated magnitude,
zero, equality in condition 2, or a failed bound is rejected with a nonzero exit.

## Rendering (optional)

`render.py` is not a checker. It requires matplotlib, imported only when a
render is requested; NumPy arrives as matplotlib's dependency. Examples:

```sh
python3 simulations/render.py simulations/generated/sigma_0.obj simulations/generated/tile.png
python3 simulations/render.py simulations/generated/sigma_2.obj simulations/generated/patch.png
```

No paper-cited generation or exact check depends on matplotlib or NumPy.

## Exploratory period search

```sh
python3 simulations/explore/period_search.py --max-side 7 --max-cells 63
```

This is a bounded exact-cover search for registered tilings with an
axis-aligned rectangular period lattice. Its header and terminal result repeat
that `NONE FOUND` is not theorem evidence. The bounds are printed, and a node
cutoff produces `INCONCLUSIVE`, never `NONE FOUND`. A positive result prints the
period box and a complete pose witness.

The other files in `explore/` are unmodified packet discovery programs. See
`explore/PROVENANCE.md` for their source paths and SHA-256 hashes. They are not
used by the exact simulation tests.

## Tests

```sh
python3 -m unittest discover simulations/tests
```

The integration test generates refinement depths 0–2 and literal proof patches
`A_0`–`A_2`, exports the depth-indexed physical OBJ files, runs parent
recognition on literal `A_2`, checks the default family byte-for-byte, and
confirms that a deliberately repeated magnitude is rejected. Temporary test
output stays under `simulations/tests/_generated/` and is removed afterward.

## Brute-force periodicity search (no theorems)

`simulations/periodicity_search.py` is an independent, theorem-free check that a sceptic can
run: it searches for periodic tilings by SAT and grows Heesch-style coronas. Its model is
stated in its docstring in full: copies are the solid under one of the 48 signed coordinate
permutations plus an integer translation; two copies are compatible iff their carrier cells
are disjoint and every shared unit panel carries exactly opposite features (same marker
points, opposite heights), computed in exact rationals from `solid/r44_solid.json`.

```sh
python3 -m venv .venv && .venv/bin/pip install python-sat      # one-off (CaDiCaL bundled)
.venv/bin/python simulations/periodicity_search.py --controls   # must find periodic tilings
.venv/bin/python simulations/periodicity_search.py --selftest   # both encodings agree
.venv/bin/python simulations/periodicity_search.py --index 32 --coronas 4
```

- `--index N`: for every full-rank sublattice of Z³ of index ≤ N (Hermite normal forms; 7 of
  index 2, 13 of index 3, 35 of index 4, …) decide whether the torus R³/L can be tiled.
  A solution would lift to a periodic tiling with period lattice L; UNSAT for all lattices
  up to N means no such tiling with a fundamental domain of at most N cells.
- `--coronas K`: for k = 1..K, decide whether the seed copy can be surrounded so that every
  cell within Chebyshev distance k is covered exactly once by pairwise compatible copies.
- `--controls`: the unit cube (periodic at index 1) and the featureless chair carrier
  (periodic at index 7: the chair alone tiles by translation) must both be found, which
  shows the search can find periodic tilings when they exist and that the features are what
  block them.
- `--selftest`: the compact "slots" encoding and the transparent pairwise encoding must
  give identical verdicts on 292 small instances (9 of them satisfiable).
- Progress is printed in place with an ETA; `--verbose` prints one line per lattice; the
  JSON receipt goes to `--out` (default `simulations/periodicity_search_report.json`) and is
  rewritten after every index and every corona radius (`status: in progress` until the run
  ends), so an interrupted long run still leaves a receipt of everything it established.

Caveats printed by the tool itself: grid-registered copies only (an assumption of this
search, not derived from the proof); a bound N is evidence, never proof; tori detect only
full-rank period lattices.
