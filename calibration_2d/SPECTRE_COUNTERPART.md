# The Spectre as a second planar counterpart

Tier T2, exploratory. This note is outside the calibration campaign and proves
nothing about R44. It records what an exact computation on the planar Spectre
monotile (the chiral sibling of the hat) says about the same quantities that
`LESSONS_FOR_3D.md` asks to measure, set beside what `simulations/` computes for
R44. The Spectre numbers come from the fork `brentharts/spectre` (exact sympy
arithmetic on the published substitution, plus a Lean 4 file that checks the
closed forms); they are not re-derived in this repository.

## The comparison

| Quantity | Spectre (d = 2) | R44 (d = 3) |
| --- | --- | --- |
| linear inflation lambda | (sqrt 6 + sqrt 10)/2, lambda^2 = 4 + sqrt 15 (Pisot) | 2 |
| supertile boundary growth per level, nu | 2 + sqrt 5 = phi^3 | 4 = lambda^2 |
| order of the exact boundary recurrence | 3, characteristic polynomial (x-1)(x^2-4x-1) | 1 (24 * 4^N) |
| closed form | P(k) = 2 F(3k+5) + 4 (Fibonacci), proved in Lean for all k | 24 * 4^N, proved in Lean for all N |
| D_b = log nu / log lambda | 1.39925 | exactly 2 |
| fractal excess D_b - (d-1) | +0.3993 | 0 |
| fields of area and boundary growth | Q(sqrt 15) and Q(sqrt 5) | both Q |
| boundary direction histogram | 12 directions, golden split (even/odd classes F(3k+4)+1, F(3k+3)+1) | exactly flat, 4^(N+1) per axis direction |
| source of pure-point structure | Pisot unit, irrational window (planar) | integer inflation 2, 2-adic window, modular coincidence at depth 3 |
| orientation transfer matrix | zero sector not semisimple (Jordan pair) | `simulations/orientation_spectrum.py`: x^3 (x-8)(x-2)^20, semisimple, frequencies 1/24 |
| interface counts at coarseness c | (T(c) P(N-c) - P(N))/2 | the same form: 12 * 4^N * (2^c - 1) |
| chirality | strict: reflections globally forbidden | strict: all 44 legal contacts are proper rotations; 1,194 of the 2,388 raw contacts are mirror placements and none is legal |

## What this says about the 3D lessons

* The R005 lesson is "search for a small geometric state and conserved or
  expanding quantities". The Spectre boundary is such a state: an order-three
  integer recurrence whose characteristic polynomial factors as a marginal
  eigenvalue times a golden quadratic, and whose closed form is Fibonacci.
  For R44 the corresponding state is trivial, which is a finding: the supertile
  surface of the doubling hierarchy is an ordinary surface, so no fractal-boundary
  mechanism is available to R44 and none is needed.
* "Measure growth in all directions": for R44 the boundary faces are flat across
  the six axis directions at every depth. The planar tilings do not behave this
  way, so a 2D intuition that boundary directions are skewed does not transfer.
* The Pisot structure that the planar tilings use to turn geometry into arithmetic
  (irrational frequencies, pure-point diffraction) is absent for R44: the
  inflation is the integer 2 and every orientation frequency is rational. R44 gets
  pure-point structure the other way, from a 2-adic internal space, through the
  modular coincidence recorded in `THEOREM.md` (cited T3 step to the diffraction
  statement). `simulations/coincidence_rate.py` adds the rate at which that
  coincidence sets in: c(M) = 28*2^M - 48 undetermined digit words at depth M, so
  the undetermined set in Z_2^3 has box dimension 1.

## Caveats

The planar numbers rest on the substitution table of the Spectre as published,
transcribed in the fork; an audit, not a proof, ties it to the published tiling.
The counts of boundary direction classes are made on the placed tiling through
k = 6 and are not proved for larger k. The Lean statements certify arithmetic on
counted values, not the counts themselves.
