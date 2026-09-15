# Ask your AI to audit Chair44 (R44) — T3 reading; T2 execution; T1/T1n formal audit

This utility is not evidence for the theorem. It organizes the supplied proof and checks.

Does this package establish that the specified solid tiles three-dimensional Euclidean space
and that every tiling by congruent copies has no nonzero translation period? Independently
examine the argument, challenge its definitions and global implications, and run checks if
your environment supports execution. Explain your findings to me. Identify exactly what
you checked and what remains unverified.

Assume nothing in the archive is correct. Seek a concrete counterexample or a precise
unsupported inference, each with its exact location. This instruction adapts the opening
of the repository's standing external-review brief; no earlier verdict is supplied.

Do not consult any prior review; none is in this package. State which model you are
(including version if known), the date, and whether you executed anything. Read START_HERE.md
first. The text bundle includes actual core Lean definitions/theorems and selected literal
data, but not the complete execution dependency tree. The companion zip contains bulk
certificate tables, imported proof sources and executable checkers. Record that limitation
without treating it as a missing proof.

Use HOLDS-AS-STATED / FAILS / INCONCLUSIVE for the overall verdict and for each finding,
always with a file:line location. Give the strongest attack first. Include all five of
these required sections, ordered by the strength of your findings:

1. Could the tiling definition accidentally exclude unwanted tilings?
2. Where is existence proved independently of aperiodicity?
3. What forces arbitrary orientations into the discrete contact analysis?
4. Does coarsening preserve the actual rule?
5. Does the formal theorem concern the same solid the reader sees?

Separate execution limitations from mathematical findings. A successful computation alone
does not resolve an unexamined mathematical implication. Hashes establish byte identity;
inspect the definitions and the bridge from generated data to the formal solid as well.
Use the axiom-set vocabulary: T1 = Lean with standard axioms only; T1n = Lean with named
native compiler hooks as well; T2 = finite Python computation; T3 = written proof or cited
import. Infer formal tiers from axiom sets, never from tactic spelling. Historical D/Q/C
ledger labels describe definitions/quotations/citations, not additional proof tiers.

With Python, run `python3 reader/check_package.py`, then the commands in START_HERE.md.
With sufficient Lean resources, run the documented build and controls and diff fresh
axiom output against the supplied log. Otherwise label the logs as supplied records,
not a fresh build. Report what would change your verdict.
