# ---
# jupyter:
#   jupytext:
#     text_representation:
#       extension: .py
#       format_name: percent
#   kernelspec:
#     display_name: Python 3
#     language: python
#     name: python3
# ---

# %% [markdown]
# # Can Chair44 (R44) fill space without ever repeating?
#
# **Run it yourself.** Choose **Runtime → Run all** in Colab. Then rotate the tile,
# inspect an overlap, change a shell index, or deliberately break a certificate.
# Code is folded; expand it whenever you want to inspect the calculation.
#
# > “$Q$ admits a tiling of $\mathbb{R}^3$.”
# > “Every tiling $T$ by $Q$ has $\operatorname{Per}(T)=\{0\}$.”
# > “Every tiling $T$ by $Q$ has $|\operatorname{Sym}(T)|\le24$.”
# > — paper §3 (Existence) and §7 (paper macros expanded for display; congruent copies include reflections).
#
# **This notebook is a reader utility, not evidence for the theorem.** Its finite
# computations are **T2**. **T1** means Lean with standard axioms only; **T1n** adds
# named compiler hooks; **T3** means written proof or cited import. Pictures use
# floats for display only. The formal build is a separate action at the end.
#
# A fresh local Jupyter run on host `ai-box` took 98 seconds on 2026-09-11
# (Python 3.12). Your own runtime, host and date are recorded below. A hosted
# Colab timing is not yet available. The setup fetches a fixed source snapshot,
# not today's main.

# %% tags=["hide-input"]
# This import is expanded by build.py so the downloadable notebook stands alone.
from runtime import Session
# These assignments are filled from reader/pin.json and its generated evidence map.
PIN = {}  # R44_PIN
CLAIM_MAP = {}  # R44_CLAIM_MAP
session = Session(PIN, CLAIM_MAP)
session.prepare()

# %% [markdown]
# ## 1. What is the shape?
#
# **T2 · display only.** Drag to turn the tile. Select **Diagram**, then **Use true
# scale**, to see the actual feature footprints and heights. Try **Periodic
# cousin** and **Try a true period** to explore the featureless chair.
#
# The embedded viewer is the repository's existing viewer. Its source hashes are
# checked before it is shown. The next cell runs the mesh and finite certificate
# checks; their complete output is saved with your session.

# %% tags=["hide-input"]
session.run("viewer", session.viewer, "T2 source data; display only")

# %% tags=["hide-input"]
session.replay()

# %% [markdown]
# ## 2. Why do the tiny features matter?
#
# **T2 · exact collision witness.** This example shows two copies implicated in
# a rejection witness and the retained-core overlap box in yellow. Rotate it to
# inspect the overlap. Coordinates below the picture are exact fractions.
#
# Choose a different record (0–5272) and rerun the cell. `partner_index` selects
# a companion within that record. The original packet's integer checker runs
# first; only the resulting display coordinates are converted to floats.

# %%
record_index = 0  # @param {type:"integer"}
partner_index = 0  # @param {type:"integer"}
session.collision(record_index, partner_index)

# %% [markdown]
# ## 3. Which neighbours can fit?
#
# **T2 · finite companion census.** Expand the fresh report below. The companion
# census and the physical collision-box replay have separate checks. Their
# scope statements describe exactly what each computation establishes.

# %% tags=["hide-input"]
session.companions()

# %% [markdown]
# ## 4. Why must tiles form larger groups?
#
# **T2 · parent-completion certificates.** Select a shell (0–32). The central
# tile and its recorded neighbours are shown together; the recorded parent role
# and contact indices are printed above them.
#
# This v1 displays certificate data and replays its checks. Recognizing a patch
# you supply is a future U2 integration, not an operation of this notebook.

# %%
shell_index = 0  # @param {type:"integer"}
session.parent(shell_index)

# %% [markdown]
# ## 5. Why does the argument keep working?
#
# **T2 · compare the actual contact sets.** This executes the registered checker
# and displays both set differences, rather than reading a precomputed Boolean.
# Expand the result to inspect all contacts yourself.

# %% tags=["hide-input"]
session.atlas()

# %% [markdown]
# ## Try to break a certificate
#
# **T2 · six mutations.** Run the cell to test the six existing corruption controls.
# Select a result to inspect its rejection. Each corruption is confined to a
# temporary copy; the original inputs are checked again afterwards.

# %% tags=["hide-input"]
mutations = session.mutations()
from IPython.display import Markdown
for result in mutations["tests"]:
    display(Markdown("**" + result["mutation"] + "** — `" + result["last_error_line"] + "`"))

# %% [markdown]
# **T2 · your turn.** Choose one corruption and an index, then run this cell.
# The index addresses a triangle, a feature, a rejection witness, or a legal
# contact, depending on the selected corruption. The unchanged checker decides
# the result; an unexpected error is reported as a failed experiment.

# %%
mutation_name = "missing_triangle"  # @param ["missing_triangle", "reversed_triangle", "changed_geometric_apex", "missing_rejection_witness", "wrong_companion_quantifier", "missing_registered_contact"]
mutation_index = 0  # @param {type:"integer"}
session.mutation(mutation_name, mutation_index)

# %% [markdown]
# ## Try something that really repeats
#
# **T2-adjacent · evidence only, used nowhere in the proof** (paper §8.1).
# Run the periodic unit-cube and featureless-chair controls, then inspect their
# explicit witnesses. This installs the optional `python-sat` dependency if
# needed. It does not run the long R44 periodicity search.

# %% tags=["hide-input"]
session.controls()

# %% [markdown]
# ## 6. Does this settle the infinite problem?
#
# **T1 / T1n / T3 · read the argument and its dependencies.** The map below is
# generated from the paper's ledger and the supplied axiom log. Each declaration
# has its own axiom-derived tier. Expand a source to read its exact proof text.
# Finite experiments above do not execute the infinite-space argument.

# %% tags=["hide-input"]
session.sources()

# %% [markdown]
# ## Check the formal proof
#
# **T1 / T1n · separate execution environment.** The logs above are supplied
# records, not a fresh Lean build. A full build needs roughly 16 GB RAM and a
# multi-gigabyte dependency download; budget 30 minutes or more after dependencies.
#
# [Open the prepared Codespace](https://codespaces.new/ioannist/six-birds-tiles)
# · [Read the build instructions](https://github.com/ioannist/six-birds-tiles/blob/main/notebook/LEAN.md)
#
# Opening the environment does not launch the build. The instructions give one
# command that builds the pinned sources, runs controls, compares fresh axiom
# output with the supplied log, and writes a separate execution receipt.

# %% [markdown]
# ## Keep your results
#
# **T2 · session record.** Download your unsigned receipt to keep or give to your
# AI. It includes the source hashes, host, date, timings, failures and skipped
# steps. This Python notebook always records `lean_ran: false`.

# %% tags=["hide-input"]
session.download()
