# proof/ERRATA.md — review-driven clarifications (no change to the mathematics)

The proof documents are verbatim from the packets. Each item below is a MINOR finding from
proof/review/ with the repair the paper text must carry. None restricts the theorem.

| # | Location | Finding | Repair | Source |
|---|---|---|---|---|
| E1 | ALIGNMENT_PROOF.md Lemma 4.3, first sentence of the proof | the chosen base-edge point must avoid the finite exceptional set of §2.2 as well as the companion graph's vertices for Lemma 3.2 to apply | "choose a point avoiding the vertices and the finite exceptional set"; such a point exists on the nondegenerate edge | Eddy r1, greddy r1 (implicit) |
| E2 | PROOFS_registered.md Theorem 8.1 | "the small-collar realization lemma" is invoked but never stated under that name | state it: a locally finite baseline chair tiling whose profiles match on every shared panel is carried to a Q-tiling by the glued tube homeomorphism (ALIGNMENT_PROOF.md Lemma 6.2 / PROOFS_registered.md §1.3); add that the macro adjacency graph is connected because the unit-cell adjacency graph is | Eddy r1, greddy r1 |
| E3 | ALIGNMENT_PROOF.md Lemma 3.2 | "integer multiples of π/2" should recall that a face containing the line contributes a half-plane of angle π (§2.2) | one cross-reference | greddy r1 |
| E4 | PROOFS_registered.md Theorem 10.1 | parent origins may all lie in (1,1,1)+2Z³, so D(T) may sit on a half-integer coset after halving | note that periods are differences of poses in one coset, hence still in Z³; the halving argument is unchanged | greddy r1 |
| E5 | PROOFS_registered.md §6 native asymmetry; THEOREM.md row | the T2 check compares the 192 heights only under the six coordinate permutations; the reduction from all of Isom(R³) to those six is the planar-area argument (T3) | keep the row split: reduction T3, six-permutation comparison T2; the Lean phase-1 theorem extends the finite comparison to all 48 signed permutations | greddy r1 |
| E6 | ALIGNMENT_PROOF.md Lemma 6.2 ("no other edit touches its interior core") | the sentence alone does not establish that the entire tile is mapped to the intended modified copy | add the ownership argument the construction already supplies: every feature tube belongs to its two incident baseline cells, both with unique owners in the component; a tube not on a tile's exposed boundary is disjoint from that tile's material, so the glued map sends each baseline tile exactly onto its Q-copy | external review 2026-09-08 (m2) |
