# Adversarial review request — proposed rational polyhedral 3D Einstein R44

Do not assume the result is correct. The packet proposes one unmarked compact polyhedral 3-ball Q of volume 7 that tiles R^3 by congruent copies but allows no nonzero translation or infinite-order screw symmetry in any tiling. Reflections are explicitly allowed.

The exact model is `results/r44_solid.json`; the OBJ is merely convenient visualization. Run `python src/replay.py`, but do not mistake successful finite checks for independent validation of the geometric alignment proof.

## Highest-priority task

Audit Sections 2–5 of PROOFS.md as a proof about **arbitrary Euclidean tilings**, not a grid tiling. Find a counterexample or certify each inference independently:

1. Actual mesh angles are only pi/2, pi, 3pi/2, and pi +/- alpha_j, pi +/- beta_j, with all 24 small deviations distinct. Does the generic edge-sector argument necessarily force a complementary feature edge, without a face-to-face assumption?
2. Every point of a feature graph has solid angle >7pi/4 because the local graph slope is <=3/25. Does this prevent every switch of partner along an edge and at the connected marker's vertices?
3. From one partner for the complete graph, equal edge types/lengths and no collinear continuations force an exact matched pyramid. Does that correctly restrict relative orientation to a cubic signed permutation and shifts to the eighth grid?
4. Audit the 6,862-pose completeness argument. For each of the 5,273 rejected nonoverlapping mates, the exhibited feature's EVERY possible isolated companion overlaps the other baseline body. Eighth-grid overlaps survive the retained-core erosion. Is the quantifier over companions correct, including when the marker belongs to the second tile?
5. Do the 44 surviving integral feature mates force a whole connected component to cover every grid cell, and then all of physical space? Could an unregistered tile remain outside that component or fill a gap overlooked by the collar argument?

A failure in any of these would restrict the result back to its registered-carrier theorem. Please separate that outcome from failure of the finite registered proof.

## Second task: registered recognition and recurrence

Reconstruct the exact cover of 22 shell cells by the 44 full-body neighbors. Check that there are 33 possible shells. Audit the proposed-parent signatures, all central-neighbor completions (14 completable outer cases, 18 impossible outer cases, one central shell), and all 28 parent conflicts.

Then independently reconstruct all 697 candidate parent contacts, allowing odd translations before filtering. There should be 116 body-disjoint cases and exactly 44 admitted cases, all even; after dividing translations by two, this must be equality of pose sets with the original atlas, not equality of counts.

Check that the decoded parents therefore obey the same geometry and that the period-halving argument applies indefinitely. Verify the explicit nested existence construction from the same-frame grandchild at (2,2,2).

## Third task: physical object and claim scope

Check that the rational mesh is an embedded boundary of a 3-ball, not merely a watertight complex of Euler characteristic two. The supplied ambient tube homeomorphism is intended to prove this. Confirm the minimal core, all feature clearances, native asymmetry, volume 7, and finite full symmetry conclusion.

No citation or SBT law is to be accepted as a substitute for any geometric implication above. No novelty priority, Lean formalization, or external verification has been claimed. A rigorous counterexample or correction is more valuable than encouragement.
