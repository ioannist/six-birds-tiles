# Chair44 (R44) image asset inventory

Status: production complete, 2026-09-11. The inventory was revised after an
adversarial Claude Fable 5.1 review and again after owner review of the produced
assets. Palette, typography, feature visibility and small-format tests are
defined in [`VISUAL_DIRECTION.md`](VISUAL_DIRECTION.md).

## Production rule

Every depiction of Chair44, the plain-chair control, a compatible cluster, or
a tiling patch is rendered programmatically from the repository's canonical
geometry and placement data. Generative imagery may supply backgrounds,
lighting concepts, textures, decorative motifs and layout ideas, but it must
not draw, reshape, complete, obscure or reinterpret a mathematical object.

Critical copy, numerical data, labels, hashes and QR codes are typeset during
deterministic composition. AI may draft that material, but generated lettering
is not used in a final factual asset. This keeps the geometry and the claims
auditable while allowing the surrounding campaign to have a strong visual
identity.

Production is pinned to one clean source commit through `reader/pin.json`, and
its four canonical digests are asserted before rendering. Publication status
and all public claims come from a separate reviewed claim/copy file, not from
status strings embedded in geometry exports. The final plate records the
object, author, date and source identity; it does not use “first” or make a
legal-priority assertion.

The canonical solid is `solid/r44_solid.json`, SHA-256
`f320d7a0c2d784a3eb29f001dc035808f67591d9ea8d3dd45949e66442f0ed55`.
Colours are always identified as annotations; Chair44 is one unmarked solid.
Features may be enlarged only in explicitly labelled explanatory insets. New
campaign illustrations use the paper's single convention, bases ×5 and signed
heights ×80. True-geometry renders remain the default. No asset may imply that
the chosen numerical dimensions are special: congruent complementary features
and the encoded profile are the operative facts. The older panel image in
`figures/` uses a labelled ×25 height convention and is not reused in the new
campaign without relabelling or regeneration.

## P0 — reconstruction and priority plate

### I01. Chair44 reconstruction plate

**Status: complete.** The owner replaced the proposed numerical tables with a
direct visual specification after reviewing R1. R2 is the approved form.

This is the archival image intended to carry the priority claim and enough
visible mathematical information to reconstruct the solid without trusting a
perspective drawing.

**Content**

- Title: `Chair44 (R44) — an aperiodic three-dimensional monotile`.
- Author: `Ioannis Tsiokos`.
- Project attribution: `with ChatGPT Astra + Six Birds Theory`.
- Permanent project address: `www.EmergenceCalculus.com/r44`.
- A proof-submission status line immediately below the title, followed by a
  short, carefully scoped theorem statement from the reviewed claim/copy file.
- One principal isometric render and six face-on directions.
- The seven-unit-cube carrier definition: a 2 × 2 × 2 cube with one corner
  removed, with an explicit coordinate convention.
- Every one of the 192 features is marked directly on the solid exactly once
  across the six face-on views. A signed number gives its height coefficient;
  coral filled circles denote bumps and sky outlined circles denote dents.
- The compact common construction convention gives the eight standard feature
  sites on each unit panel, the square base size and the height divisor. With
  the numbered views and carrier definition, this is enough to reconstruct the
  realization without a 192-row transcription.
- The generator derives the label projections from the Blender camera and
  canonical JSON, then asserts that the six views partition roles 0–191 and
  panels 0–23 exactly once.
- Canonical JSON hash, repository commit, plate revision, UTC generation date,
  project credit and a QR code to the pinned source remain visible but quiet.
- A notice identifies the feature glyphs as annotations and explains that the
  selected dimensions are a convenient realization rather than the source of
  aperiodicity.

**Deliverables**

- Archival master: A1 landscape SVG and vector PDF. PDF/A conformance is not
  certified.
- Raster master: 9,933 x 7,016 PNG at approximately 300 dpi.
- Web reading copy: 4,000 px wide PNG, intended to be zoomed.
- Machine audit: a JSON receipt recording all input/output hashes and the
  exact-once feature/panel coverage checks.

**Design**

An elegant technical plate rather than a patent drawing: dark neutral field,
warm ivory drafting panels, restrained coral/sky feature annotations, crisp
fine rules and generous hierarchy. A generated background may add subtle
depth, but must remain outside the locked geometry and data layers.

## P1 — public explainer

### I02. “Why Chair44 is remarkable” infographic

**Status: complete.**

A single-page introduction for readers who will not begin with the paper.

**Narrative**

1. **One unmarked shape:** show the exact tile and a magnified real feature.
2. **It fills space:** show the exact eight-copy compatible cluster, identified
   as a doubled-chair cluster rather than a scaled decorated tile, and a larger
   finite patch, explicitly labelled as a finite view.
3. **A similar chair repeats:** show the plain seven-cube chair as a negative
   control, visibly separated from Chair44.
4. **No tiling has a translation period:** state the quantifier “every tiling”
   and show the proved unique hierarchy as the step that makes any hypothetical
   translation period repeatedly halve until it cannot remain a nonzero
   lattice vector. Label this as an argument diagram, not a simulated tiling.
5. **Check it yourself:** point to the viewer, notebook, AI review package,
   paper and exact solid.

The copy must distinguish “this displayed patch does not repeat” from the
universal claim about every possible tiling. It must also say that the tiny
features restrict how copies can meet, without suggesting external matching
rules; their particular visual scale is not the source of aperiodicity.

**Deliverables**

- Primary: 2,000 x 2,500 PNG (4:5 portrait) and PDF.
- Wide adaptation: 2,400 x 1,350 PNG (16:9).
- Accessible transcript and alt text.

### I03. Exact multi-angle beauty sheet — deferred

A less technical companion to I01: one large three-quarter view, front/top/
side views, underside/rear views, and two feature close-ups. It shows all
surfaces clearly but refers reconstruction readers to I01 for the numerical
specification. Produce it only if I01 and the transparent views in I12 do not
already serve this need.

**Deliverables:** 3,000 x 2,400 PNG and a print PDF.

**Disposition:** not produced. I01 R2 and I12's transparent view library cover
the intended use without another near-duplicate sheet.

## P1 — social launch set

These are coordinated crops from one campaign system, not unrelated designs.
Each includes the quiet deterministic footer `Ioannis Tsiokos · with ChatGPT
Astra + Six Birds Theory · EmergenceCalculus.com/r44`. It remains visible but
secondary to the asset's claim.

### I04. Discovery hero

**Status: complete.**

The strongest single-tile portrait: exact Chair44 floating against a cinematic
field. At 600 px and above it uses one source-derived visibility device: either
a labelled true-geometry macro inset or canonical feature map. At 320 px it
uses a feature-map ribbon beside the tile; at 160 px the exact silhouette and
name stand alone. Copy: `One shape. It tiles space. No tiling has a translation
period.` This becomes the source of the video thumbnail so both campaigns
share one hero.

**Exports:** 1280 × 640 GitHub social preview, 1200 × 630 Open Graph,
1920 × 1080 landscape, 1080 × 1080 square, 1080 × 1350 portrait and
1080 × 1920 story, plus a 320 px review render of the square.

### I05. Scale reveal — optional/fold into I04

**Status: folded into I04's feature-map treatment.**

The exact tile beside a uniformly magnified true-geometry close-up and, only if
needed, a separately labelled ×5/×80 explanatory inset. Copy explains that the
shape alone restricts which placements fit: there are no colours, labels or
matching rules on the tile. Fold this into I04 unless testing shows it deserves
a separate post.

**Exports:** 1080 x 1350 and 1080 x 1080.

### I06. One tile to a space-filling patch

**Status: complete.**

A staged exact fixed-tile nested sequence: 1 copy, 64-copy patch and 4,096-copy
finite view. Copy: `One solid. A hierarchy without translation periods.` The
eight-copy doubled-chair cluster belongs in I02 and is not spliced into this
sequence. Every stage is labelled `Finite view`; the image says explicitly
that the exclusion of periods is the theorem, not a property inferred from the
picture. Per-copy colours are labelled as annotations. Any level-of-detail
render that omits surface features says `Carrier view — surface features
omitted`.

**Exports:** 1920 x 1080 and 1080 x 1350.

### I07. The negative control

**Status: complete.**

A split composition comparing the plain chair with Chair44. The two
objects use equal camera, scale and neutral material. Copy: `Almost the same
shape. One admits a repeating tiling; the other admits none with a translation
period.` The explicit periodic construction is attached only to the plain
chair and labelled `Plain chair — admits a periodic tiling`; Chair44's
universal claim is stated separately. Its audit receipt records the lattice
basis and determinant-7 coset check used for the control.

**Exports:** 1920 x 1080 and 1080 x 1350.

### I08. Why a translation period fails

**Status: complete.**

A restrained argument diagram showing successive registered tilings
`T`, `D(T)`, `D²(T)` and their integer-grid period vectors `p`, `p/2`, `p/4`.
It identifies unique parent recognition and registration as the substantive
steps, with repeated halving as their consequence. Exact tile clusters anchor
the diagram. Copy: `Local geometry forces a unique hierarchy. The hierarchy
leaves no nonzero translation period.`

**Exports:** 1080 x 1350 and 1080 x 1080.

### I09. Verify it yourself

**Status: repository-first version complete. Hosted URLs remain a later text
update when supplied by the owner.**

A utility-led card showing five entry points: interactive viewer, executable
notebook, AI review package, paper and canonical solid. This asset is updated
when the hosted viewer and notebook URLs are available. Until both links are
live, its public version points only to repository downloads.

**Exports:** 1200 x 630 and 1080 x 1350.

### I10. Author and project card — fold into I11

**Status: folded into I11's final verification card and the shared footer.**

A quiet final card used as the end of the carousel rather than as a standalone
post: Chair44 silhouette,
`Ioannis Tsiokos`, `Chair44 (R44)`, `ChatGPT Astra + Six Birds Theory`, and
`www.EmergenceCalculus.com/r44`.

**Exports:** 1080 x 1080 and 1080 x 1350.

## P2 — optional campaign extensions

### I11. Four-card carousel

**Status: complete.**

1. The object and claim.
2. Plain-chair periodic control versus Chair44.
3. Exact space-filling patches and the hierarchy argument.
4. Ways to inspect and verify the result.

**Export:** four 1080 x 1350 cards, with safe zones for Instagram, LinkedIn,
Bluesky and X crops.

### I12. Press and presentation kit

**Status: complete.**

- Transparent-background exact renders from six directions.
- Hero render with empty space on the left and a mirrored composition with
  empty space on the right.
- 16:9 title slide, 16:9 theorem slide and A4 press image.
- Caption, short description, long description, credit line and short, medium
  and long alt text.

## Shared production components

Build these once and reuse them across the inventory:

- A locked exact-render library: tile, plain-chair control, feature macro,
  eight-copy cluster, 64-copy patch and 4,096-copy finite patch.
- A camera manifest recording projection, display basis, pose, full camera
  matrix, focal length and crop for every render.
- A claim/copy file from which deterministic overlays and accessible text are
  generated. It fixes the image-footer string as `Ioannis Tsiokos · with
  ChatGPT Astra + Six Birds Theory · EmergenceCalculus.com/r44` and supplies
  short, medium and long alt text for every
  asset. Social assets use pinned DejaVu Sans/DejaVu Sans Bold to match the
  video; I01 and viewer-facing assets use the viewer's Georgia/Helvetica
  system.
- A campaign palette and type system compatible with the video and repository
  figures, with pinned font files and licences.
- AI-generated background plates with no mathematical object or lettering.
  Their prompts, generation settings, seeds when available, and file hashes
  are recorded even when exact regeneration is unavailable.
- A compositor that places locked renders and exact copy over those plates.
- A receipt for every asset containing the pinned commit and source hashes,
  renderer/version, geometry hash, camera manifest, output hash and, for an
  arrangement, exact poses, patch level or lattice basis and relevant check
  outputs.
- Automated checks for output dimensions, required credit/URL text, canonical
  solid digest, and accidental feature exaggeration without disclosure. The
  compositor also proves that alpha-masked geometry pixels are byte-identical
  before and after compositing, and strips or normalizes timestamps so builds
  are deterministic. Feature-map receipts confirm the canonical visible-symbol
  count. Exact-tile/plain-carrier difference tests determine whether physical
  relief is actually visible at each export size; invisible relief is never
  presented as a readable distinction.
- A per-asset posting-copy file carrying the current proof-submission status,
  links, credit and accessible descriptions outside the image itself.

## Proposed production order

1. Pin the source commit; build the locked render library, camera manifest,
   claim/copy file, receipt schema and copy lint.
2. Produce I04 to establish the campaign look and shared video thumbnail.
3. Produce I07 with the same camera and its exact periodic control.
4. Produce I01 revision 1 with complete data and orthographic views; visual
   polish may change later without changing its locked data layer.
5. Produce I06 from the fixed-tile nested sequence.
6. Assemble I02 from the audited components above.
7. Publish I09 when hosted links are live. Produce I08, I11 and I12 after the
   core set is approved; defer I03, standalone I05 and standalone I10.

The minimum initial launch set is I01, I04, I06 and I07. I02 follows in the
first revision cycle; I09 joins the set when the hosted links are live.
