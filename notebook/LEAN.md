# Run the formal proof in your own session

**T1/T1n (by axiom set). This utility adds no evidence for the theorem.** It lets
you run the existing Lean sources and record what your own session did. The
Python notebook reads the committed logs as **supplied records, not a fresh
build**. This separate environment performs the resource-intensive build.

[Open GitHub Codespaces](https://codespaces.new/ioannist/six-birds-tiles)
on the branch containing these reader utilities, or open the repository in
VS Code and choose **Dev Containers: Reopen in Container**. The configuration
requests at least 4 CPUs, 16 GB RAM and 32 GB storage. Codespaces uses
[`hostRequirements` to restrict eligible machines](https://docs.github.com/en/codespaces/setting-up-your-project-for-codespaces/configuring-dev-containers/setting-a-minimum-specification-for-codespace-machines).
Local Docker users must allocate the resources themselves.

No proof build or Mathlib download starts when the container opens. When ready,
run this in its terminal from the repository root:

```sh
python3 notebook/run_lean.py --repo . --output /tmp/r44-lean-session
```

Budget 30 minutes or more for the build, plus the multi-gigabyte Mathlib cache
download. A fresh AI-package build on the authors' host took 26 minutes 53 seconds,
with 9.8 GB peak resident memory. These are supplied
measurements, not measurements on your host. The receipt records your elapsed
times. Use a new output directory for every attempt. Download any results you
want to keep before deleting or rebuilding the Codespace.

The runner exports only selected committed inputs with `git archive` at
`838bca514679b2531d31f4e0dfd66641269e2a8c` (the reconciled reader snapshot;
mathematical baseline `d90313a717994936f254990f88d2624bbcce5bcd`). It asserts and
prints all four canonical data digests before checks or toolchain setup. Your
checkout may contain later reader utilities; the proof build always uses this
pin. If the commit is missing from a shallow checkout, fetch it first:

```sh
git fetch origin 838bca514679b2531d31f4e0dfd66641269e2a8c
```

The source export excludes private thread exports, `.codex/`, `.agents/`,
`offgit/`, `history/`, `archive/`, review directories and `.lake/`. It includes
seven historical delivery ZIPs because the unchanged
`scripts/discharge_diff_audit.sh` compares current proof sources against them.
Those are required inputs to the provenance control, not prior review verdicts.

The container installs the `elan` manager. The runner reads `lean-toolchain`
from the exported sources and installs that version (`leanprover/lean4:v4.31.0`).
It then executes these commands from the exported `lean/R44` directory:

```sh
lake exe cache get
lake build
bash scripts/controls.sh
```

The controls themselves rebuild the promoted-root regression target, check the
delivery diffs and admissions, run the expected-failure controls and compile the
positive scope examples. The runner then explicitly elaborates
`R44/Axioms.lean` again to obtain fresh dependency lists and compares the full
result with the supplied log, which it preserved before any build.

Results appear in `/tmp/r44-lean-session/`:

- `receipt.json`: unsigned session metadata, commands, exit codes, wall times,
  skipped steps, full fresh axiom output and diff, and the `CONTROLS:` summary.
  `lean_ran` becomes true only after the build, controls and fresh audit finish
  successfully. Earlier partial execution is listed even if this flag is false.
- `supplied_records/`: the original committed `build_axioms.log` and
  `negative_control.log`, explicitly labelled as supplied records.
- `build.log`, `controls.log`, `fresh_axioms.log` and other stage logs: this
  session's actual output. Watch a running stage with `tail -f` on its log.
- `fresh_build_axioms.log` and `axioms.diff`: fresh dependency lists and the
  complete textual difference. A nonempty diff returns a nonzero exit status
  and needs examination; it is not automatically a mathematical failure.

Read the axiom sets using [AXIOMS.md](../lean/R44/AXIOMS.md): T1 uses standard
Lean axioms only; T1n additionally uses the named `native_decide` hooks. The
build's tactic choice alone does not determine a tier. The receipt does not
merge a separate Python notebook replay: its `replay_report` is null and its
explanation says that replay was not run here.

For a cheap setup check without any Lean execution or downloads:

```sh
python3 notebook/run_lean.py --repo . --output /tmp/r44-lean-prepare --prepare-only
```

This checks export exclusions, canonical digests and all delivery-audit inputs,
and saves the supplied logs. Its receipt says `PREPARED_ONLY`, `lean_ran: false`
and lists the skipped build stages. Neither this nor reading supplied logs is
a fresh Lean build.
