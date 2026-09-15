# R44 film: one shape, no periodic tiling

Revision 2 adopts **Chair44 (R44)**, adds the author/project credits and website,
extends the end card to 4:06, and removes numerical feature-size callouts.
See [END_CARD_REVISION.md](END_CARD_REVISION.md) and the current
[captions.json](captions.json). The plan and review history below describe
the original version.

Status: **FINAL production plan — Fable 5.1 closure review: READY**, 2026-09-11. This document
records the approved plan; production status is now tracked in [PRODUCTION.md](PRODUCTION.md). Caption master: [CAPTIONS.srt](CAPTIONS.srt), with machine-readable
cue times in [captions.json](captions.json). Target: a four-minute film that
works without narration, followed by an optional 30–45-second trailer cut from
the finished shots. Do not replace the main film with a short turntable.

## Purpose and audience

Give a curious visitor three experiences: see a beautiful, tangible 3D object;
watch the almost-identical plain chair repeat; understand what R44's tiny
features change and why a finite animation alone cannot establish a universal
negative. Lead naturally to the viewer, notebook and AI review package.

The mathematical target is the paper's full-space claim, not visual disorder:
R44 admits tilings by congruent copies, and every such tiling has no nonzero
translation period. The theorem also permits reflections, derives homochirality,
and bounds every tiling's full symmetry group by 24.

Terminology correction for production: the plain chair IS a monotile (one shape
that tiles). It is NOT an aperiodic monotile, because it has a periodic tiling.
It is the negative example for the desired property and a positive control for
showing an actual period. Never caption it “not a monotile.” Do not say that R44
has no repeated local patterns, no symmetry whatsoever, only one tiling, or
that disorder is what makes it aperiodic. Avoid “first ever” and other priority
claims. Present the repository's proof submission and its evidence accurately.

## Story and art direction

Working title: **R44 — One shape. No periodic tiling.** Open with the finished
object and the promise, then earn that promise through a comparison and a
construction. The dramatic beat is at 82 seconds: an arrangement that worked
for the plain chair physically fails when the tiny features return. The film
must then answer both “does R44 tile at all?” and “why can none of its tilings
repeat?” Existence and universal nonperiodicity get separate scenes.

Use a dark ink/navy studio, warm ivory satin surfaces, broad soft key light,
cool rim light and restrained coral/blue highlights. Solid objects should feel
precise and substantial. Prefer an oblique orthographic camera for assembly,
and a restrained perspective macro camera for the feature close-up. Flat face
normals preserve the actual polyhedron. No bevel modifier or displaced shader
may silently change the canonical geometry. Highlights come from lighting and
materials. Avoid mirrorlike surfaces, excessive bloom, shallow depth of field
that hides a contact, dramatic shaking, particle explosions or incessant spins.

Colour encodes the current explanation only: neutral ivory for the real object;
coral/blue to distinguish two touching copies; temporary family colours for
hierarchy; an outlined tick for a verified periodic alignment. Clear these
annotations before changing their meaning. Show all copies in one material
again at 139–146 seconds. A red overlay is never the only indication of failure:
show the overlapping solids and label the issue. Legibility must survive
colour-blind viewing and a muted 720p preview.

Music is optional: a restrained original or appropriately licensed instrumental
bed, with quiet placement sounds and a brief pause at the failed contact.
The argument must remain complete with audio muted. No narrator is required;
if added later, narration follows the caption script rather than introducing
new mathematical claims.

## Shot-by-shot direction

The captions in the next section are the exact proposed on-screen script.
Times below include reading holds; transitions do not steal those holds.

| Time | Picture and action | What the viewer should understand |
|---|---|---|
| 0:00–0:21 | 0:00–0:06: true-scale hero; 0:06–0:13: pull back to a verified patch. At 0:13, cut into a true-geometry panel macro and hold until the surface relief is unmistakable. The title settles without covering the feature. Label the macro “True geometry — magnified view.” | The object and the question. This is a 3D space-filling claim, not a floor mosaic. |
| 0:21–0:36 | Continue the panel macro into cue 4: show the now-visible features flattening. Label the transition “Feature removal illustration.” Pull back to the plain chair in the same pose by 0:28. A temporary seven-cell exploded diagram counts the cubes, then closes into the single carrier. Label “plain chair — features removed.” | The comparison changes only the features. The seven cubes are an explanatory decomposition, not seven tile types. |
| 0:36–1:06 | Assemble the explicit periodic chair tiling. Lock the camera. An outlined ghost of the same arrangement translates by one lattice vector, settles, then takes another equal step. Repeat the alignment in an interior comparison window, with a visible buffer beyond it. Show a small repeat-cell lattice diagram. | A real, indefinitely repeatable translation exists for the plain chair. A finite patch's exposed boundary is not the period test. |
| 1:06–1:22 | Restore features in a side-by-side single-tile comparison. Travel from a true-scale view into a true-geometry macro. One separated diagram may enlarge the features, persistently labelled with its scale factors. Show “24 panels × 8 features = 192”; show the true height range relative to a unit edge. | Almost the same silhouette; exact geometric features rather than colour instructions. |
| 1:22–1:40 | Return to the plain chair's exact lattice positions, now populated with canonical R44. Use the enlarged 1:22–1:33 interval to travel into the preselected pair and hold on a stationary true-proportions section. The two solids intersect as their positive features enter the opposing material; show the overlap bracket. Recenter the macro on the feature and uniformly change scene units to avoid tiny-coordinate render artefacts; keep the mathematical proportions unchanged. Then pull back and ask whether another arrangement works. | One demonstrable arrangement fails. This is not presented as the universal aperiodicity proof. |
| 1:40–2:03 | A clean scene, explicitly “R44 — valid patch.” Place the hidden central child first, then reveal the other children in a readable order. Ghosted travel becomes opaque only at the exact final pose. End on an eight-copy cluster, with its chair carrier outline, not an asserted doubled corrugated solid. | Copies really fit; hierarchy starts with eight. Placement paths are presentation, not a physical assembly protocol. |
| 2:03–2:19 | Cut to the literal nested construction. Fix the original tile in world coordinates and grow A0 → A1 → A2: 1 → 64 → 4,096 copies. Add the actual set difference in spatial/hierarchical waves. Camera pulls back as the boundary expands in three directions. End with a section or open corner exposing interior layers. | Growth is compatible and genuinely volumetric. The clip displays a finite part of a construction continued in the proof. |
| 2:19–2:40 | Remove family colours; keep exact positions. For the universal-claim caption, freeze and overlay “every tiling,” not “this sample.” Show two copied local motifs only if an exact translated-pose comparison identifies them. If that check finds none for the chosen crop, omit the motif overlay; never approximate a match. | Same unmarked shape throughout; local recurrence is compatible with aperiodicity. |
| 2:40–3:04 | Reveal parent outlines and successive larger carrier groupings. Separate three schematic stages: carrier grouping, rescaling, fresh standardized R44 copies. Persistent label: “coarsening diagram — surfaces re-standardized.” | The hierarchy is forced and unique; the operation preserves a valid tiling. The union of eight decorated tiles is not literally a scaled decorated tile. |
| 3:04–3:27 | Transition to a spare registered-grid diagram. A generic hypothetical vector p accompanies panels T, D(T), D²(T), … and becomes p/2, p/4, … . Show the integer-grid requirement and the statement “p/2ⁿ ∈ Z³ for every n ⇒ p = 0.” Use an optional example p=(4,0,0) only in a separately labelled illustration; it reaches 1/2 and fails, but is never asserted to be an R44 period. | The universal obstruction is an all-level argument, not failure of a few arrows in a cropped image. Each normalized tiling has its own grid/coset; period differences have integer coordinates. |
| 3:27–3:48 | Two separated copies illustrate right/left handedness. They do not join in a fabricated rejected contact. Show whole-patch reflection as permissible; mixed-handed tiling as theorem-excluded. Then use a small schematic screw-axis symbol labelled “no screw symmetry with a nonzero slide,” and the explicit bound ≤24. | The theorem is stronger than eliminating an obvious translational grid. Finite rotational symmetry remains possible. |
| 3:48–4:00 | Return to the true-scale plain-material hero and a wide patch. End card with repo name/URL, three actions and a quiet credit “Construction and proof submission: see repository.” | Beauty, precise takeaway, and a concrete way to check the work. |

The negative-example film occupies about 79 seconds including the restoration
failure; actual R44 assembly/growth receives 39 seconds, plus the opening and
closing patch views. Do not let the proof diagram crowd out seeing the object.

## Complete caption script

Every item below is a caption cue, not a narrator outline. Display at most two
main lines at once. Source tags are production metadata, not extra text to burn
into each frame. Persistent labels and titles listed separately below are also
part of the screen design.

| Cue | Time | Exact caption |
|---|---|---|
| 1 | 0:00–0:06 | One solid shape. |
| 2 | 0:06–0:13 | It can fill three-dimensional space. |
| 3 | 0:13–0:21 | Yet none of its tilings repeats by translation.<br>Meet R44. |
| 4 | 0:21–0:28 | First, remove its tiny surface features. |
| 5 | 0:28–0:36 | What remains is a chair made from seven cubes. |
| 6 | 0:36–0:44 | This plain chair also fills space. |
| 7 | 0:44–0:53 | Slide the outlined strip by this vector.<br>It lands on identical chairs. |
| 8 | 0:53–0:58 | The same translation works again. And again. |
| 9 | 0:58–1:06 | One repeating tiling is enough:<br>this chair is not an aperiodic monotile. |
| 10 | 1:06–1:14 | Now restore R44’s 192 tiny bumps and dents. |
| 11 | 1:14–1:22 | Their heights range from 1/10000 to 12/10000<br>of a unit edge. |
| 12 | 1:22–1:33 | Keep the chairs in that repeating arrangement.<br>These copies now overlap. |
| 13 | 1:33–1:40 | So that arrangement fails.<br>But ruling out one arrangement is not enough. |
| 14 | 1:40–1:47 | Can R44 fill space at all? |
| 15 | 1:47–1:55 | Yes. Here are actual copies<br>in compatible positions. |
| 16 | 1:55–2:03 | Eight copies form a cluster<br>shaped like a doubled plain chair. |
| 17 | 2:03–2:11 | Larger compatible patches grow<br>around a fixed tile. |
| 18 | 2:11–2:19 | The construction extends to fill all of space.<br>The screen shows only a finite part. |
| 19 | 2:19–2:26 | Every copy is the same shape.<br>Colours only help us follow the construction. |
| 20 | 2:26–2:33 | The claim concerns every tiling of R44—<br>not just the one being built here. |
| 21 | 2:33–2:40 | Local patterns can recur.<br>The whole tiling cannot repeat by translation. |
| 22 | 2:40–2:48 | Why? The geometry forces a unique hierarchy. |
| 23 | 2:48–2:56 | Chairs group into larger chairs,<br>then larger chairs again. |
| 24 | 2:56–3:04 | The proof recovers a valid R44 tiling<br>after each grouping and rescaling. |
| 25 | 3:04–3:12 | A translation period would survive each step,<br>with its vector halved every time. |
| 26 | 3:12–3:20 | At every level a period has integer coordinates<br>in that level’s registered unit grid. |
| 27 | 3:20–3:27 | Only the zero vector can keep being halved<br>and still have integer coordinates forever. |
| 28 | 3:27–3:34 | Rotations and reflections were allowed.<br>No colouring or matching rules were imposed. |
| 29 | 3:34–3:41 | Even so, a tiling cannot mix the tile<br>with its mirror image. |
| 30 | 3:41–3:48 | Every tiling has at most 24 symmetries.<br>None is a screw motion with a nonzero slide. |
| 31 | 3:48–3:54 | One connected solid. Shape alone.<br>An aperiodic monotile in three dimensions. |
| 32 | 3:54–4:00 | Explore the tile. Run the notebook.<br>Ask your own AI to check the proof. |

Persistent screen labels:

- “True geometry — magnified view” on the opening panel macro; “Feature removal
  illustration” during flattening. Both are required labels checked by the
  delivery validator, not optional shot-table notes.
- “True proportions — magnified section” on the overlap close-up; “no screw
  symmetry with a nonzero slide” on the final screw-axis schematic.
- “R44 — true geometry” for the canonical object; “Plain chair — features removed”
  for the periodic comparison. Keep both labels in split views.
- “Features enlarged: bases ×5, heights ×80” for the separated illustrative
  macro diagram, matching the paper's figure convention. True contact shots
  use the actual mesh and camera magnification, not widened/tallened features.
- “Exploded assembly illustration” while copies travel; remove it only after
  settlement. Translucency indicates transit, not an admissible partial tiling.
- “Finite view” on the cropped global arrangements; “Compare inside this window”
  for the periodic overlay. Use ticks, outlines and words, not colour alone.
- “Coarsening diagram — surfaces re-standardized” for 2:40–3:04; “Hypothetical
  period” and the current normalized grid scale for 3:04–3:27.
- “Colours identify copies; they are not matching rules” when family colours
  first appear. Do not keep large explanatory labels on every beauty shot.

Main captions: large high-contrast sans serif, 1080p equivalent 46–54 px,
semi-opaque lower background, 8% safe margins; mathematically typeset labels
separate from prose. Maximum two lines and at most 48 characters per line. `captions.json` is the
single text/timing master; generate the SRT and this document’s caption table
from it. Lint line count, line length, cue order, overlaps, duration and reading
rate (at most 3 words/second) before every delivery. The current 32-cue script
passes these checks. Reflow text or edit the master rather than shrinking type. Hold the cue for its complete interval.
Display fractions cleanly; `1/10000` is a proportion, not a claim about millimetres.
Proof submissions/review status belong in the description/evidence notes, not
faux certificates or “AI approved” badges over the tile.

## Exact data and mathematical checks before scene construction

Pin the mathematical sources to `838bca514679b2531d31f4e0dfd66641269e2a8c`, using
`reader/pin.json` and its four canonical SHA256 values. Assert all four before
any geometric check. Export required tracked inputs with `git archive`; never
read proof/data from an accidentally modified working tree. Record additional
hashes for the archived patch generator, source excerpts and rendering scripts.
Exclude private thread exports, `.codex/`, `.agents/`, `offgit/`, history,
archives, `.lake/` and prior review directories from any distributable bundle.
Do not modify the solid, certificates, verifier, Lean project or paper.

Geometry: import rational vertices/triangles from `solid/r44_solid.json`, not a
hand-remodelled chair and not the viewer's default Jewel approximation. Maintain
one exact canonical mesh and linked instances with exact integer poses. Convert
to floats only at the rendering boundary. Keep separate named meshes for the
featureless comparison and labelled illustrative feature diagram. Never apply
geometry-changing beautification to a mesh called canonical.

### Periodic comparison: a constructive positive witness

Reuse the viewer's basis
`b1=(-2,1,0), b2=(-1,-1,-1), b3=(-1,0,2)` and the plain carrier P. Show a buffered
finite subset of the translates P+l, l in L=<b1,b2,b3>, all in the identity frame.
Use `b1` for the clearly visible repeated slide; orient the camera so its
projection is long enough to read. The cube may appear for a one-second scale
reference, but is not the main comparison: the almost-identical chair is stronger.

The completed planning checks are recorded in [PLANNING_CHECKS.json](PLANNING_CHECKS.json).
The planning check confirmed determinant 7. The function
`r(x,y,z)=(x+2y+4z) mod 7` vanishes on all three basis vectors, and the seven carrier
cells occupy residues 0 through 6 exactly once. Thus the lattice equals the
kernel and the carrier cells are complete coset representatives. This gives a
finite exact certificate of the infinite lattice tiling; it is not a SAT search
that merely happened to find a large patch. Preserve this check in the production
receipt. No floating tolerance is involved.

The moving overlay compares tile identities/poses in an interior window whose
required preimages exist in both crops, including two successive b1 shifts.
Generate the extra buffer first. Do not wrap the finite R44 crop periodically,
count missing boundary copies as failures, or label a finite 100% match as the
reason a global period exists. The infinite positive witness is the lattice
construction above.

### Concrete restoration failure

An exact planning check using the canonical `Tile`, `FramedTile` and `Placed`
panel data from `simulations/periodicity_search.py` found:

| Quantity | Value |
|---|---|
| Frames of both copies | identity |
| First/second translations | `(0,0,0)` and `(2,-1,0)=-b1` |
| Shared feature centre | `(2,1/4,3/8)` |
| Outward normal of first panel | `(1,0,0)` |
| First/second outward heights | `3/2500 = 12/10000`, `1/5000 = 2/10000` |
| Overlap along the central normal | `7/5000 = 14/10000` |

Their baseline carriers do not overlap. At that feature, both positive pyramids
extend into each other. Recompute exact feature identities/indices from the
archived source, save them and use these same triangles in the macro shot. A
point on the normal strictly inside both pyramids and a small rational box
around it should be checked before drawing a volumetric overlap highlight;
the current planning check establishes the central overlap, not yet that box.
A section showing the true two pyramids and their overlap interval is the
primary visual; no unchecked volumetric highlight is required. Recenter the
rendering scene at the feature centre and uniformly rescale all objects, lights
and camera distances, retaining a conversion back to canonical units. Label it
“True proportions — magnified section.” Uniform rescaling does not exaggerate
the relief relative to its base. Test ray offsets, clipping and contact shading
in this scene before final rendering. Any optional height-only exaggeration
must be a separate diagram labelled with its exact factor. Do not substitute an unrelated collision certificate
witness while claiming it comes from this periodic lattice.

This rejects this particular feature-restored lattice arrangement only. Keep
cue 13's transition to the universal problem. The shape could in principle
have had some other periodic tiling; excluding all of them uses the paper.

### R44 assembly, nesting and hierarchy

Reuse `simulations/patches.py`: `sigma_depth`, `nested_patch`,
`check_two_refinement_embedding`, `check_nested_pair` and `check_patch`.
Single refinement counts 1,8,64,512 are not the literal fixed-origin exhaustion.
Use sigma1 for the eight-copy assembly shot, then make a clearly staged cut to
A_n = sigma_(2n) - c_n(1,1,1), c_n=2(4^n-1)/3. The latter has 1,64,4096 copies for
n=0,1,2. The planning check confirmed exact same-frame set inclusion for those
three levels. Never move existing tiles while claiming the scene is this nested
growth. Animate only A_(n+1) minus A_n, using spatial waves and hierarchy bands
without falsely labelling arbitrary intermediate subsets as completed tilings.

Verify determinant +1 of construction frames, distinct poses, carrier-cell
ownership and every completed-patch face contact against the 44-contact atlas.
Those are finite checks; continuous-solid correctness is tied to the canonical
mesh/profile checks and the paper's realization theorem. Do not present a cell
occupancy test as an independent proof of exact surface compatibility.

For eight-copy entry paths, do not assume a collision-free rigid assembly path
exists. Place the hidden central copy first for visibility and use ghosted,
labelled exploded transitions. Only final poses are claimed as valid geometry.
No rigid-body simulation is needed. Do not show opaque solids physically passing
through each other as if this were a demonstrated construction method.

For hierarchy overlays, use exact construction groups. If the film says the
viewer is seeing recovered parents, run `simulations/parents.py` on complete
interior shells and use its certificate results. Boundary shells remain
undetermined. Prefer “hierarchy illustration” in this film; don't imply that
colouring by construction order proves unique recognition.

The coarsening shot must visibly distinguish carrier grouping from replacing
surfaces. Section 6 explicitly says the operation is not a homothety of the
corrugated cluster into Q. Do not morph eight decorated tiles into a perfectly
scaled Q and call it literal equality. The proof's covariance is
`D(T+v)=D(T)+v/2`; hypothetical period vectors belong to the successive tilings
T, D(T), D²(T), not to a single fixed tiling at progressively smaller shifts.

### Caption-to-evidence map

| Cues | Supporting source / scope |
|---|---|
| 1–3, 20, 32 | `paper/tex/sec1_intro.tex`, main/full theorems; `LogicalSpine.lean:r44_einstein`. The captions summarize the submitted theorem, not a new empirical finding. |
| 4–9 | Exact periodic-carrier lattice check above, matching `viewer/index.html:COUSIN_BASIS`; `simulations/README.md` periodic controls. One witness suffices to refute forced aperiodicity of the carrier. |
| 10–11, 19, 31 | `paper/tex/sec2_solid.tex`: 24 panels, 192 marks, exact feature dimensions, rational coordinates, volume 7; canonical JSON. Connected/topological-ball assertion also uses boundary and realization evidence. |
| 12–13 | Exact panel-pair restoration failure above; narrowly scoped to those poses. |
| 14–18 | `paper/tex/sec3_finding.tex` existence, `simulations/patches.py` and exact nested-pose checks. The infinite conclusion is supplied by the proof, not a rendered horizon. |
| 21–27 | `paper/tex/sec6_hierarchy.tex`, coarsening/hierarchy; `paper/tex/sec7_aperiodicity.tex`, no-period proof. Local recurrence is not denied; the only obstruction claimed is global. |
| 28–30 | Introduction's allowed motions; section 7's homochirality, finite symmetry and screw-motion consequences. A nontrivial screw motion here has nonzero axial translation. |

The authoritative phrasing and theorem premises come from the paper, whose
relevant passages must be included verbatim in the production evidence notes.
Captions are short editorial summaries of those passages, not replacement proof
prose. For formal labels use axiom sets only: T1 standard axioms, T1n additional
named native compiler hooks; do not classify by tactic name. Existing build logs
are supplied records; rendering this film runs no Lean proof build.

## Fully programmatic production architecture

Use a stable pinned Blender release with Python scripting, Cycles for the final
render and a faster low-sample preview using the same scene. Blender runs in
background mode; camera, object poses, animation, lights, render settings and
outputs are created by code. No mouse/keyboard UI automation. FFmpeg assembles
numbered frames, captions and optional audio. Inspect stills/contact sheets and
short previews as images/video, then revise the scripts.

Proposed implementation files (not yet implemented):

| File | Responsibility |
|---|---|
| `video/export_scene_data.py` | Archive/pin/hash checks; canonical mesh, lattice, fixture and nested-pose export; exact receipts. |
| `video/scene_config.json` | Palette, cameras, lighting, output settings, seed, selected Blender/FFmpeg versions. |
| `video/shots.py` | Named shot intervals, exact settled poses, staging poses, parent overlays and camera curves. |
| `video/build_scene.py` | Build the reusable mesh instances, materials, lights and collections; save `.blend`. |
| `video/render.py` | Render selected frames/shots in background; resume after interruption; collect timings. |
| `video/compose.py` | Frame/audio/caption composition, MP4/WebM, contact sheets and thumbnail. |
| `video/check_delivery.py` | Validate identity, settled poses, timing/caption sync, required scale labels and output completeness. |

Keep exact arrays immutable and separate from animated display transforms.
The source convention is `world_i = sign_i * local_perm[i] + translation_i`.
Document the matrix convention and test transformed basis vectors. Blender’s
Z-up preference must not silently permute coordinates: any global display
basis change is applied consistently to meshes, poses, normals and overlays.
Use stable tile IDs from frame+translation, not enumeration order that can change
between patch levels. Instance the mesh rather than writing thousands of OBJ
copies. For the far 4096-copy shot keep canonical mesh instances if performance
permits; any feature-omitted LOD must be confined to an explicitly labelled
“carrier view — surface features omitted” shot, never the contact comparison or
the unqualified hero. Do not let invisible LOD changes silently define the object.

Render shots separately with a frame-index timeline. At 30 fps the master has
7,200 frames, indexed 0–7,199; cue times use half-open intervals. Deterministic
quaternion interpolation reaches the prescribed proper rotations; all settling
keyframes are validated before render. Use minimum-jerk easing for arrival,
subtle stagger and locked reading holds. Avoid a continuous camera orbit while
the audience must judge a periodic overlay or a contact failure.

Separate 3D frames from text composition so caption revisions do not trigger
full rerenders. Preserve a caption-free master plus SRT. Fonts must be embedded
or reproducibly installed with suitable redistribution terms; mathematical
labels must use actual glyphs, not screen captures from editors.

### Output and performance choices

Primary deliverable: 1920×1080, 30 fps, four-minute H.264 MP4 with captions, plus
caption-free MP4 and SRT. Produce a high-quality mezzanine, WebM web copy, still
thumbnail and the short trailer from the same timeline. A 4K master is optional
only after measured cost is acceptable; it is not a reason to delay 1080p.

Benchmark representative hero, overlap, eight-copy and 4096-copy frames before
scheduling the full render. Test samples/denoising on those frames for stable
fine features and no temporal flicker. Use a short moving preview to check it;
a clean single still is insufficient. Pin the successful device backend and
settings. Compute wall-clock estimates from measured seconds/frame, including
I/O and composition; 7,200 frames at 2/10/30 seconds each require roughly
4/20/60 GPU-hours. These are arithmetic scenarios, not host benchmarks.

Render PNG or EXR sequences with per-shot manifests and atomic completed-frame
markers; restart only missing or invalid frames. Archive render settings and
frame hashes. Keep large `.blend` files, sequences and temporary output under
an ignored output path until the publication storage decision is made. Never
check private reviewer transcripts into the public film bundle.

## Production sequence and review gates

1. **Plan review — complete.** Fable 5.1 reviewed the story, captions, negative
   control, quantifiers, coarsening, rendering plan and accessibility. The
   revised plan received READY in a focused closure review; see the record
   below. The returned model metadata confirms `claude-fable-5-1`.
2. **Data preflight.** Archive and hash inputs; generate the exact comparison,
   overlap fixture and nested poses; save checks. This gate is about choosing
   truthful pictures, not performing new mathematical research.
3. **Three style frames.** Hero, restored-feature overlap section, and large
   patch. Compare lighting, readable details and caption layout at 1080p/720p.
4. **Motion proof of concept.** A 10–15-second periodic slide/overlap clip and
   a 5–8-second eight-copy assembly clip. Resolve visual ambiguity and transit
   conventions before completing the film.
5. **Full rough cut.** All four minutes at preview quality, with exact captions
   and temporary audio. Check pacing, interior 3D readability, crop/buffer logic
   and all context labels. Have an independent viewer explain the difference
   between “this tiling looks nonperiodic” and “the shape forces nonperiodicity.”
6. **Final rendering.** Only after the chosen preview has a clean science and
   visual review; render incrementally and compose. No additional user permission
   is inherently required by this plan; follow the owner's authorized scope.
7. **Delivery check.** Verify all frames, duration, subtitle times, no clipping,
   source hashes, true/exaggerated labels, exact contact fixture, valid settled
   poses, unchanged persistent tiles in nested growth, and readable end card.
   Reviewers must see the final movie, not just its source code.

Definition of production success: an unfamiliar viewer can state that both
shapes tile, one explicitly repeats, R44's theorem excludes a period in every
possible tiling, local patterns can recur, and colour has no mathematical role.
The viewer should remember the tiny features and the growth into space, not
just the notation. All explanatory labels must remain readable on a phone.

## Deliverables and publication handoff

- Final film, caption-free film, SRT, thumbnail, short trailer and optional WebM.
- Reproducible scripts/configuration, pinned source manifest and exact finite
  check receipts; short `video/README.md` with one build/render command per stage.
- `video/EVIDENCE.md`: source quotations, caption-source map, fixture coordinates,
  display conventions and what the film does/does not establish.
- Description text linking the paper/repository, app, notebook and AI package.
  Hosted app and notebook URLs are awaiting the owner; keep configurable null
  values, never fake links. The repo URL is `https://github.com/ioannist/six-birds-tiles`.
  For the draft end card use that real URL. Before public release, either supply
  the two hosted links or explicitly point to the working repository downloads;
  do not promise live services that have not been published.

No publishing, expensive rendering, modelled replacement geometry or changes
to the proof are authorized merely by finalizing this planning document.

## Review record

Independent reviewer: **Fable 5.1**, requested through Claude CLI as
`claude-fable-5-1`; the successful call's `modelUsage` confirms that identifier.
The short alias `fable-5.1` returned a 404/unrecognized-model error. Review scope
was the film plan, captions, mathematical communication and production feasibility,
not an independent theorem verdict. Raw output remains in
`offgit/video_plan_review/`; it is excluded from distribution.

The first review returned **FIX-FIRST** for caption layout and opening visibility,
with no blocking mathematical objection. The following changes were applied:

| Finding | Resolution |
|---|---|
| Overlong caption lines | Shortened cues 3, 19, 25 and 26; balanced cues 15 and 17 over two lines; JSON generates SRT/table; lint enforces two lines, 48 characters, timing and reading rate. |
| Features invisible before removal | A labelled true-geometry macro starts at 0:13, continues through feature removal, then pulls back to the plain chair by 0:28. |
| Microscopic overlap difficult to render | Primary visual is a magnified true-proportions section; recenter and uniformly change scene units; test ray offsets. No unchecked volumetric highlight. |
| Ambiguous title | “One shape. No periodic tiling.” replaces “No repeating tiling.” |
| Screw-motion ambiguity | Cue 30 explicitly says “a nonzero slide”; scene label matches, retaining finite rotational symmetry as possible. |
| Undefined carrier-cluster terminology | Cue 16 uses “a cluster shaped like a doubled plain chair,” accompanied by a carrier outline rather than literal surface equality. |
| Proof-submission credit | End card says “Construction and proof submission: see repository.” |
| Timing of dramatic beat | Shortened repeated-slide hold; moved restoration earlier; cue 12 now receives 11 seconds, 1:22–1:33. Total duration remains four minutes. |

The focused Fable 5.1 closure review returned **READY** and confirmed that all
32 captions, their times, line breaks and three script representations agree.
The CLI metadata again confirms `claude-fable-5-1`. Its non-blocking request to
replace the remaining screw-scene label was applied, and the new opening-macro,
removal and overlap labels were added to the required-label checklist. These
final label edits were self-checked after the READY review.

Production checks of the actual images, exact scene fixtures, phone readability
and render performance remain future work; a reviewed plan does not close those
gates. No video rendering or changes to mathematical sources occurred in this
planning task.
