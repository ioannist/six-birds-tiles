# Additions from the Spectre fork

Contributed from `brentharts/spectre`, where the same Chair44 data was rebuilt
independently. Everything here is tier T2 or exploratory: finite computations
and numerical evidence that bear on no theorem and on none of the Lean-checked
statements in `lean/R44`. Where a script is standard library only it says so;
the optional ones need `sympy`, or `numpy` and `scipy`, and live under `explore/`.

| Item | Run | Needs | What it shows |
| --- | --- | --- | --- |
| `orientation_spectrum.py` | `python3 simulations/orientation_spectrum.py` | stdlib | the 24x24 orientation transfer matrix of the eight children: characteristic polynomial x^3 (x-8)(x-2)^20, minimal polynomial dividing x(x-8)(x-2), so the zero sector is semisimple; every row and column sums to 8; orientation frequencies tend to 1/24 with error exactly (1/4)^d. All eigenvalues are integers and the inflation is 2, so the Pisot route to pure-point diffraction and the irrational-frequency witness of aperiodicity do not apply to R44; the 2-adic route recorded in `THEOREM.md` replaces them. The aperiodicity theorem does not use either. |
| `coincidence_rate.py` | `python3 simulations/coincidence_rate.py` | stdlib | an independent rebuild of the 168-label cell substitution (primitive at power 3; least modular-coincidence depth 3 with (0,0,2) among 336 of 512 coincident addresses, as upstream), plus a rate: the digit words not yet coincided number c(M) = 28*2^M - 48 from M = 3 (176, 400, 848, ...), the transfer matrix on the 41 non-singleton label sets has spectral radius exactly 2, so the undetermined set has box dimension 1 in the internal space Z_2^3. The pure-point and limit-periodic conclusions remain the cited T3 import. |
| `explore/lean/CoincidenceRate.lean` | `lean simulations/explore/lean/CoincidenceRate.lean` | Lean 4, no library | the closed form 28*2^M - 48 from the recurrence, for every M. Standalone, outside the lake project. |
| `surface_laws.py` | `python3 simulations/surface_laws.py` | stdlib | for depth N = 0..4: boundary faces 24*4^N, shared faces 12(8^N - 4^N), 4^(N+1) boundary faces in each of the six axis directions, and interface counts B_c = 12*4^N*(2^c - 1) = (T(c)P(N-c) - P(N))/2. The supertile boundary grows by 4 = 2^2, so log 4 / log 2 = 2 = d - 1: an ordinary surface. |
| `explore/lean/SurfaceLaws.lean` | `lean simulations/explore/lean/SurfaceLaws.lean` | Lean 4, no library | the counting identities above for every N, with axioms limited to propext and Quot.sound. Standalone; not part of the `lean/R44` lake project or its ledger. The counts themselves are geometry and come from the script. |
| `explore/symbolic/symchair44.py` | `python3 simulations/explore/symbolic/test_symchair44.py` | sympy | R44 regenerated from nothing in exact sympy (cells, panels, grid, substitution by exact cover, labels by signed union-find over the exact-complement equations), printable as LaTeX with `--latex --pdf`. Its mesh, children, 192-label profile, 2,388 raw contacts, 44 legal contacts, 30 realized states and 372 site equations (rank 180, kernel 12) equal the canonical solid and `certificates/candidate_certificate.json`; the volume is exactly 7 for all base width w and height unit h because the labels sum to zero. A second route, not a proof. |
| `explore/smooth/chair44_rigidity.py` | `python3 simulations/explore/smooth/chair44_rigidity.py --quick` | numpy, scipy | for smooth (non-pyramid) height fields with the same orbit structure, a numerical scan of sliding, rotated, mirrored and tilted neighbours for exact complements. Only lattice contacts complement; the best non-lattice candidates are isolated minima of an overlap mismatch, never zero. Evidence for the smooth variants, not a proof, and the margin shrinks with smoothness. Covering-argument hypotheses are in the docstring. About 2.5 minutes. |
| `explore/smooth/chair44.py`, `chair44_family.py` | imported by the above | numpy | exact combinatorics and orbit-projection height fields used by the rigidity scan. |
| `explore/smooth/chair44_blender.py` | `python3 chair44_blender.py [depth]` | Blender | builds supertiles and patches in Blender, coloured by hierarchy digit. Not exercised by tests. |
| `../calibration_2d/SPECTRE_COUNTERPART.md` | read | | the planar Spectre next to R44: boundary recurrence and its Fibonacci closed form, boundary dimension 1.399 versus 2, orientation spectra. |

## A note on chirality

`THEOREM.md` already makes R44 strictly chiral for the registered tilings
(reflected and unreflected tiles cannot co-occur). The independent computation
agrees at the level of contacts: of the 2,388 raw face contacts, 1,194 place a
mirror image against the root, and none of the 44 legal contacts is a mirror.
The undecorated seven-cube chair has six symmetries, three of them mirrors, and
is achiral; the decoration leaves only the identity.

## Tests

`python3 -m unittest discover simulations/tests` now also runs
`tests/test_additions.py` (stdlib). The sympy generator has its own test,
`explore/symbolic/test_symchair44.py`, skipped when sympy is missing.
