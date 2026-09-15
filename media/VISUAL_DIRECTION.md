# Chair44 (R44) visual direction

Status: reviewed direction, 2026-09-11. Revised after an adversarial Claude
Fable 5.1 review.

## Existing visual language

The campaign should grow from the implemented viewer and video rather than
introducing another identity.

### Palette

| Role | Colour | Use |
|---|---:|---|
| Deep field | `#1b2540` | primary background |
| Secondary navy | `#26325a` | panels and quiet divisions |
| Warm ivory | `#f4ecdf` | the unmarked tile and primary text |
| Secondary cream | `#e9dfcc` | cards and technical fields |
| Coral | `#e8563f` | bump / positive polarity |
| Sky | `#5aa9e6` | canonical dent / negative polarity colour; supersedes “teal” and “blue” in campaign copy |
| Mustard | `#f3b53a` | titles, calls to action and proof-path accents |
| Muted blue-grey | `#5d6478` / `#c9cfe0` | secondary copy, depending on ground |

Coral and sky are reserved for feature polarity when one tile is shown.
Multi-copy scenes use the viewer's eight-colour copy palette and state that
colour identifies copies. Mustard remains an editorial accent and does not
encode geometry.
The viewer's mustard-to-coral Height ramp is not used in campaign assets.

### Typography

- Social set I04–I11: the video's system, with DejaVu Sans Bold titles, mustard
  uppercase kickers and DejaVu Sans body copy.
- Plate I01 and viewer-facing assets: Georgia Bold display with Helvetica Neue,
  Helvetica and Arial body copy, matching the viewer.
- Critical data uses tabular numerals. All final lettering is typeset by the
  compositor, with font files and licences pinned where redistribution allows.

### Composition

Use the viewer's navy field, cream surfaces and restrained coral/sky/mustard
accents. The website's geometric editorial inspiration can appear as large,
flat background forms or cropping devices. Those forms must not resemble
additional tile geometry or imply a construction. The video contributes soft
studio light, an ivory tile, subtle floor reflection and generous negative
space.

Background forms use navy tones, cream and mustard only. Coral and sky never
appear in the background of a frame that carries a feature map. The campaign
tile uses the video's cool near-white rendered material; warm ivory remains the
flat UI, plate and text colour.

## The small-image problem

Chair44's feature bases have side 1/50 and its heights range from 1/10000 to
12/10000 of a unit edge. Size is only part of the obstacle. The pyramid facets
have slopes from approximately 0.57° to 6.8°, so a true-proportion feature can
read as flat even after uniform magnification unless it receives raking,
shadow-casting light. Magnitudes below 6 are not reliably legible even then.
At ordinary social and GitHub preview sizes, exact features are invisible or
read as compression noise. If the tile spans half a 1280 px preview, a feature
base is about 5 px wide and its height remains under 0.3 px; in a 160 px
thumbnail, the base is under 1 px and the height under 0.05 px. A true-geometry
hero therefore looks like the plain periodic chair. Making the features merely
a little larger is worse: viewers may read accidental surface roughness
without understanding that the relief carries structured information.

The viewer's Jewel mode solves visibility by replacing every tiny square
pyramid with a much larger triangular facet occupying one eighth of its panel,
raised or sunk ×40 the true height and extending into the featureless outer
band of the real panel. It preserves centres, polarities and coefficients, but
it is illustrative geometry rather than Chair44 and changes the visible
silhouette. It works as an interactive teaching mode because the UI explains
and lets the reader switch modes. In a detached social image, that disclosure
is too easy to lose. Jewel mode is never used in a campaign still.

## Recommended three-scale system

### Scale A — recognition

For thumbnails and ordinary feed viewing, show the exact near-white tile as a
clean silhouette. Do not pretend that all 192 features can be resolved. Below
320 px, the silhouette and `Chair44` name are the whole image: no feature
device appears. At 320 px and above, use one of these source-derived devices:

1. A flat `Feature map` generated from the 192 canonical centres and
   polarities, occlusion-culled to the visible panels. Filled coral squares mark
   bumps and hollow sky squares mark dents, so the distinction survives
   greyscale and colour-vision differences. Symbols use a fixed screen-space
   size. At 320 px, the map sits beside the tile as a ribbon or panel card; it
   does not decorate the solid. From 600 px upward it may sit on a translucent
   technical layer over the exact tile. Its label `Feature map · annotation`
   is inseparable from it; the reconstruction plate uses the longer
   `Feature map — annotations, not markings`.
2. A circular or rectangular magnification window connected to a real panel.
   The window is at least 300 px on its short side, shows a feature of magnitude
   6 or higher, and uses uniform camera magnification of true geometry with
   strong raking light. It does not exaggerate height and is a beauty device,
   not the primary proof of feature visibility.

The feature map is preferable when the image needs to communicate the global
distribution. The magnification window is preferable for a beauty-led hero.
The main solid underneath remains the exact canonical render in both cases.

### Scale B — explanation

For the infographic, comparison card and carousel, show the exact tile plus:

- a uniformly magnified true-geometry close-up;
- a source-derived panel plan with coral `+` and sky `−` glyphs; and
- when necessary, one separate schematic inset using bases ×5 and signed
  heights ×80, labelled with the exact exaggeration factors.

Never apply enlarged geometry to the whole hero tile. Never use colour alone:
polarity also uses filled/hollow symbols, `+`/`−`, outward/inward arrows, or
distinct hatch patterns. A Scale A crop uses at most one visibility device; a
Scale B crop uses at most two.

### Scale C — reconstruction

The archival priority plate shows true orthographic geometry, the complete
visible data tables and a worked feature. Its panel diagrams may use the
standard ×5/×80 explanatory convention, but the principal views remain exact.
The plate makes its geometry states explicit in a persistent legend:

- `Exact solid`
- `Uniform magnification — exact proportions`
- `Explanatory schematic — bases ×5, heights ×80`
- `Feature map — annotation only`

## How the video handles the problem

The video does not make the features legible on the opening whole-tile hero.
It labels that view `true geometry`, then uses time and camera motion to travel
into one feature. The close-up is uniformly magnified and explicitly says
`no height exaggeration`. The shallow topography remains visually subtle; the
sequence, labels and removal/restoration comparison carry the explanation. It
then removes the features as an illustration,
shows the plain-chair periodic control, returns to true Chair44 geometry and
uses separate copy colours for assemblies. Large patches omit tiny feature
geometry where it would be invisible and label the view as finite.

This temporal solution cannot be copied literally into a still. The social
equivalent is a simultaneous two-scale composition: exact whole tile plus a
true-geometry magnification window or feature-map layer.

## Rules by asset

Every social image carries the quiet footer `Ioannis Tsiokos · with ChatGPT
Astra + Six Birds Theory · EmergenceCalculus.com/r44`. It is typeset, never
generated into the background, and remains visually secondary. In video it is
visible on the closing card and is not spoken.

- **I04 hero:** exact near-white tile, raking studio light and no full-surface
  Jewel treatment. At 600 px and above use either one true-geometry macro
  window or one feature map. At 320 px use the feature-map ribbon beside the
  silhouette; at 160 px drop the visibility device entirely.
- **I05 scale reveal:** fold into I04 unless testing proves a separate post is
  useful. It is the only social asset allowed to foreground ×5/×80 geometry.
- **I06 growth:** prioritise readable copy boundaries. Omit feature geometry at
  distant levels and label this explicitly. Do not overlay 192 symbols on every
  copy.
- **I07 negative control:** use the same ivory material and camera for both
  shapes. Identify Chair44 with a magnification window or feature-map callout;
  identify the plain chair with a smooth-panel callout. Do not recolour either
  entire solid.
- **I01 reconstruction plate:** use coral/sky plus signs, arrows and hatching in
  tables; maintain exact views and explicit schematic labels.
- **I02 infographic and I08 argument diagram:** use feature maps only where the
  mechanism is discussed. Elsewhere colours indicate copies or proof stages.

## Required legibility tests

Every social master is reviewed at full resolution and at these rendered sizes:

- 1280 × 640 GitHub preview;
- 1080 × 1080 square displayed at 320 px, representing an Instagram grid;
- 600 px wide feed card;
- 320 px wide mobile feed card; and
- 160 px wide link thumbnail.

Review copies are bilinearly downscaled, JPEG-compressed at quality 75 and
encoded with 4:2:0 chroma subsampling before judgment.

- **160 px:** the silhouette is recognizable and `Chair44` has an x-height of
  at least 5 px. Any visible feature symbol is a failure.
- **320 px:** feature-map symbols remain at least 4 px on a side, have at least
  3:1 contrast against their field, and filled/hollow states remain distinct in
  greyscale. In a blind I07 pair test, a reader can select Chair44 from the
  plain chair without a hint.
- **600 px:** the visibility-device label and main claim have an x-height of at
  least 7 px. The receipt confirms that the feature-map symbol count equals the
  canonical visible-panel count.
- **All sizes:** render the exact tile and plain carrier with identical camera
  and light, then difference them. If no 3 × 3 luminance block differs by more
  than 8/255, the physical features are declared invisible and the asset must
  not imply otherwise.

Fine reconstruction data is reserved for the zoomable plate.

Before publication, test a colour-blind simulation and a greyscale export.
Coral/sky encodings pass only when their paired symbols or hatching remain
distinct. A final receipt records which visibility device each asset uses and
whether any geometry is exact, uniformly magnified, exaggerated or omitted.
