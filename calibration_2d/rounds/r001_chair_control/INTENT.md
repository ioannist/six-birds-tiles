# R001 — freeze the first geometric experiment

Candidate: the union of unit cells (0,0),(1,0),(0,1), an unmarked connected
L triomino. Its boundary is (0,0),(2,0),(2,1),(1,1),(1,2),(0,2).
Allow congruent copies, including rotations and reflections.

Operation: solve the exact-cover equation 2P = union of four congruent P.
Test: separately search for a rectangular finite union that repeats to a
periodic tiling of the whole plane. Such a filling is a positive existence
witness and a negative control for the claimed forced hierarchy.

If both succeed, record exactly what extra parent-phase information the
substitution carrier provides and why the bare geometry cannot determine it
covariantly. The next repair should target that lost information.
