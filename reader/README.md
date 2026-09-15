# Ask your AI to audit Chair44 (R44) — U5

This utility is not evidence for the theorem. It packages the supplied argument and checks
for a reader's own audit: T3 reading, T2 Python replay, T1/T1n formal inspection or execution.

Release-ready reading bundles, executable packages and their checksums are
attached to the corresponding
[GitHub release](https://github.com/ioannist/six-birds-tiles/releases). Give the
reading bundle to an ordinary AI conversation, or the executable package to an
AI that can run code.

Attach the file to a fresh conversation and paste:

```text
Verify this works. Start with START_HERE and follow the included review prompt.
Tell me what you checked, what you could not check, and any concrete problems you found.
```

The generated bundle contains the paper, actual Lean definitions and supplied axiom records;
the zip additionally carries the exact data and executable checks. Prior review
reports are excluded. Mathematical text is preserved; review-only omissions are
explicitly marked and hashed.

Give a reading-only assistant the `*-reading.txt` file and copy [the review prompt](REVIEW_PROMPT.md).
Give a coding agent the companion zip; its first file is `START_HERE.md`. The zip includes
the paper PDF rebuilt from pinned sources, original TeX, exact inputs, finite checkers,
generated claim map, Lean source and dependencies for the existing controls.

The reading bundle itself contains the full Lean foundation, logical spine, finite theorem
statements, Types and FiniteModel sources, the complete literal panel table, and supplied
axiom/control logs. Readers can inspect `Q`, allowed motions, tilings and periods directly.
`reading_notes.md` explains remaining zip-only dependencies and source precedence;
`axiom_document_comparison.json` compares the documentation's records with the full log.

Build a release from a clean checkout:

```bash
scripts/make_review_zip.sh --reader --out /tmp/r44-reader-release
```

During development, an explicit preview can be built without altering the working tree:

```bash
scripts/make_review_zip.sh --reader --preview --out /tmp/r44-reader-preview
```

Both modes obtain mathematical inputs from `git archive` at the full source snapshot
in [pin.json](pin.json). Preview mode merely allows working changes to the separately
hashed reader tooling. It never copies working mathematical files or private files.
Release mode rejects tracked changes and untracked files. Outputs are named with the
source commit and include `SHA256SUMS.txt`; preview is marked in names and metadata.
The legacy `scripts/make_review_zip.sh /absolute/output.zip` entry point remains available.

The paper's mathematical baseline, `d90313a717`, predates its reconciled paper and ledger.
Consequently one later source snapshot, `838bca514679b2531d31f4e0dfd66641269e2a8c`,
supplies all paper/proof/data files. The builder checks that its complete Lean project
(excluding prior reviews) and canonical inputs match the embedded baseline. A future
repin must update `pin.json` deliberately; no command follows `main`.

Building needs Python 3.12 or later, Git, and `latexmk` with the paper's TeX dependencies.
Reader Python execution needs only the standard library. For optional Lean execution,
budget 30 minutes or more plus the dependency download; the latest extracted-package
build took 26 minutes 53 seconds on the authors' host. PDF compilation occurs in a
temporary archive tree, with four pinned figure dependencies excluded from the final zip.
The generator also runs extraction consistency, full finite replay, six mutation controls
and the delivery-source audit in another temporary tree. It also includes and runs the
four current paper checkers cited in O10/O11/L3/L8/L9/L10: nonconvex witness, planar areas,
seed-language closure and coincidence-tree data (with their `_texutil.py` helper).
Optional periodicity-search evidence (N9) and illustration-production audits (O12) are
explicitly omitted, as are superseded experiments. It does not run Lean.

Files under `.codex/`, `offgit/`, `history/`, `archive/`, `provenance/`, `.lake/`,
all `review/` directories, and `TILE_DISCOVERY_THREAD.txt` are excluded by an allowlist
and an explicit path check, including inside nested zip archives. Existing verifier packets
and the seven original Lean delivery zips remain byte-for-byte intact. Their author briefs
are not prior third-party review reports. No review verdicts are included.

The generated map copies ledger cells and links paper `% ledger:` annotations. It checks
the frozen ledger digest and derives each formal tier from the supplied axiom set; it
does not infer a dependency theorem from neighbouring text. `claim_map.json` separates
rows from full axiom records. References to excluded research history remain quotations.

Prior-review verdicts are excluded even when copied into otherwise useful documents.
The packaged `THEOREM.md`, `paper/CLAIMS_LEDGER.md` and `paper/tex/sec8_mechanization.tex`
are explicitly labelled excerpts: prior-review status and review-only M8 row are replaced by omission markers at
the original line numbers. All mathematical text remains verbatim. Original and derived
SHA256 values and omitted line numbers are in `reader/source_excerpts.json`. The map is
generated from the frozen original ledger before excerpting; regenerating it requires the
original pinned repository ledger and TeX, whose original digests cannot be recomputed from the excerpts.
The PDF is built from the same marked TeX excerpt; all mathematical text is retained.
Lean planning/update notes and obsolete `paper/STATEMENT.md` are omitted altogether.
The reading bundle includes the cited `proof/ERRATA.md`; START_HERE distinguishes verbatim
historical packet status statements from the source snapshot's current paper/formal sources.
Builder-local home/staging prefixes
are redacted in the generated PDF presentation log.

Every manifest is unsigned. Hashes establish identity, not the semantic connection between
the JSON solid, generated data, `Q`, and the final theorem. That inspection is explicitly
part of the review prompt. Successful package self-tests are T2 checks, not a new proof.

Review gates: separate Eddy science/data-mapping review, and fresh-reader FIX-FIRST tests
with a reading-only model and an executing model from two model families. These gates
must be recorded before calling U5 complete; local assembly tests do not replace them.
