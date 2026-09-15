# Film evidence and display conventions

The film presents the repository's construction and proof submission. It does
not establish global aperiodicity by showing a finite patch or failing one
period test. No new proof prose or theorem verification is supplied here.

All source references below are to commit
`838bca514679b2531d31f4e0dfd66641269e2a8c`. `DATA_CHECKS.json` identifies the
four canonical files and every archived rendering input by SHA256. The exporter
uses `git archive`, validates the four digests, then performs exact finite
checks before converting coordinates to floats for Blender.

## Caption-to-source map

| Cues | Source or production evidence |
|---|---|
| 1–3, 14–18, 31 | `paper/tex/sec1_intro.tex`, main and full theorems; `sec3_finding.tex`, existence construction; `sec2_solid.tex`, closed 3-ball and exact mesh. |
| 4–5, 10–11 | `paper/tex/sec2_solid.tex`, definition of carrier, 24 panels, 192 features, signed heights and base width. |
| 6–9 | Exact lattice witness in `export_scene_data.py` and `DATA_CHECKS.json`; determinant 7 and complete residue representatives, with two buffered translations of the displayed strip. |
| 12–13 | Exact production fixture at translations `(0,0,0)` and `(2,-1,0)`, from canonical feature data. See section convention below. This rules out only that arrangement. |
| 15–19 | Archived `simulations/patches.py`: `sigma_depth(1)` and `nested_patch(0..2)`; exact face-contact atlas checks and literal pose-set inclusion. |
| 20–24 | `paper/tex/sec6_hierarchy.tex`, unique parent, coarsening and hierarchy theorems. Local recurrence is compatible with global nonperiodicity; no approximate repeated-motif claim is shown. |
| 25–27 | `paper/tex/sec7_aperiodicity.tex`, no-periods theorem and its period-halving argument. |
| 28–30 | `paper/tex/sec7_aperiodicity.tex`, homochirality and finite-symmetry theorems; full isometries are allowed by `sec1_intro.tex`. |
| 32 | Repository reader assets, including the notebook and AI review package. Hosted URLs remain unset; the end card uses the real repository URL. |

## Exact paper quotations

From `paper/tex/sec2_solid.tex` (the displayed `Q` is the paper's `\solid`):

> A positive $a$ is a protrusion, a negative $a$ a recess, and the rest of the panel stays flat.

> The resulting solid $\solid$ (\cref{fig:tile,fig:panel}) has rational vertex coordinates; it is
> defined once, as one unmarked shape, and the indices we use to name its features describe the
> construction and impose no rule on how copies may meet.

From `paper/tex/sec6_hierarchy.tex`:

> Every tiling by $\solid$ partitions uniquely into the eight-chair parent clusters, and the
> parent of each tile is determined by a finite neighbourhood of it.

From `paper/tex/sec7_aperiodicity.tex`:

> Every tiling $T$ by $\solid$ has $\Per(T)=\{0\}$.

> Iterating, $p/2^n$ is a period of $D^n(T)$ and hence an
> integer vector for every $n$, so $p\in\bigcap_n 2^n\Z^3=\{0\}$.

> Every tiling $T$ by $\solid$ has $|\Sym(T)|\le24$.

> In every tiling $T$ by $\solid$ all placements have the same handedness: the determinants of
> their linear parts are all $+1$ or all $-1$.

The formalization's scope is stated in `paper/tex/sec8_mechanization.tex`:

> The honest summary is therefore this: the theorem is kernel-checked modulo the named
> compiler hooks;

The film makes no “AI approved” or axiom-free verification claim. Review of
the film's communication is separate from review of the mathematical submission.

## Exact contact section

The two identity-frame copies are separated by `(2,-1,0)`, the negative of the
plain lattice basis vector b1. Their carriers have disjoint cell interiors.
At world centre `(2,1/4,3/8)`, the opposing positive feature heights are
`3/2500` and `1/5000`. The canonical base half-width is `1/100`.

The figure uses the middle section `z=3/8`. For tangential displacement `u`,
the exporter evaluates the square-pyramid section as the exact tent profile
`max(0,1-|u|/(1/100))`. Copy A occupies the side below its upper boundary,
copy B the side above its lower boundary. Their common interval at the centre
has length `7/5000`, as recorded using `Fraction` arithmetic. The gold strip
is the **intersection of the two solids**. The positive pyramids themselves
need not intersect each other away from their bases.

The two screen axes use the same pixels-per-unit scale. Camera magnification
and uniform recentering preserve proportions. No height-only enlargement is
used in the film. The cutaway is a labelled section, not a transparent solid
that has been silently substituted for the canonical mesh.

## Display conventions

- The canonical Q mesh has 2,138 rational vertices and 4,272 triangles. Blender
  uses linked mesh instances and the source's signed-permutation pose convention.
- Plain carrier, flattened-feature transition, carrier outlines, ghosts and
  proof diagrams have distinct names and labels. There is no bevel modifier.
- Colours identify copies or groups; they do not prescribe matching rules.
  The film returns to a single unmarked material after growth.
- The periodic highlighted strip is exposed to the camera and buffered along
  b1. Both one-step and two-step translated poses occur in the displayed lattice.
  Only exact settled alignments receive a check mark. The complete projected
  outline is a depth-independent annotation, not additional physical geometry.
- Assembly paths are illustrations. A moving translucent copy is not asserted
  to be part of an admissible tiling, nor is its travel claimed collision-free.
- A0, A1 and A2 contain 1, 64 and 4,096 copies. Existing tile poses are fixed.
  A finite image is not asserted to fill all space; that is the paper's result.
- Coarsening explicitly replaces grouped carriers with standardized Q copies.
  Eight corrugated Q copies are never claimed literally equal to doubled Q.
- The proof diagram displays a hypothetical period and a normalized integer
  grid at each level. Its all-level condition, not a finite list of arrows,
  supplies the argument quoted from the paper.
- Mirror copies are spatially separated. No fabricated mixed-handed contact
  test is used. Finite rotational symmetries remain possible.


## Revision 2 presentation changes

Chair44 is the public nickname for the same pinned R44 solid. No geometry or
mathematical identifier changes. Cue 11 now says that the bumps and dents
change which placements fit together; the dimension values below remain
technical evidence rather than on-screen explanatory callouts. The section
labels the overlap “Shared interior.” The end card adds author-supplied credits
and a destination, and extends the timeline by six seconds to 4:06.
