# R44 film production

Production authorized by the owner on 2026-09-11, including package installation.
Production sources, tools and media live under `video/`; private review records
are under `offgit/video_production_review/`. The mathematical sources remain untouched.

## Revision 2 — delivery complete

The owner approved the public nickname **Chair44 (R44)** and requested author,
OpenAI Astra / Six Birds Theory credits, and www.EmergenceCalculus.com/r44.
Titles, captions, teaser and thumbnail adopt the public name; formal identifiers
remain R44. The end card holds from 3:54 to 4:06, with its final six seconds
free of subtitles. The music is regenerated for the full 246 seconds.

The owner also requested a restrained correction to the emphasis on dimensions:
the feature-height caption now describes compatible placements, and the numeric
overlap callout becomes “Shared interior.” Exact rendered geometry is unchanged.

Existing 3D frames are reused; composition runs on CPU and requires no GPU.
Previous deliverables and receipts are preserved at `output/revisions/v1/`.
The Fable reviews below apply to version 1, not to the revised copy.

Both revised masters contain 7,380 frames (246 seconds); the updated teaser
contains 1,200 frames (40 seconds). Full video/audio decoding, 5,700 source PNGs,
canonical/render-data hashes, source/output hashes, subtitle/header/end-card
layout and the final audio fade all PASS in `DELIVERY_CHECKS.json`. The audio
audit accepts a fade ending in digital silence.

Local visual review inspected 246 one-second full-film samples, 40 teaser
samples, the full-resolution final credits and clean overlap, and the thumbnail.
No new visible defect was found in this revision. This was an implementing-agent
review of decoded images, not independent review or real-time playback/listening.
See the revision-specific entry and media hashes in `REVIEW_RECORD.json`.

All revision jobs are finished. GPU rendering was unnecessary; the original
3D footage was reused. Nothing was uploaded or published.


## Version 1 completed delivery

- Exact source export and data preflight: PASS. See `DATA_CHECKS.json`.
- Installed locally: Blender 4.5.13 LTS (official archive, SHA256 checked),
  Python venv, NumPy, Pillow, packaged FFmpeg 7.0.2.
- GPU: RTX 3090 **index 3**, PCI `61:00.0`, UUID
  `GPU-26fc9801-c1e9-a7f9-ae80-bb42c6e5cf93`. `nvidia-smi` confirmed the
  active Blender graphics process on that GPU. Other GPUs and workloads untouched.
- Style tests completed in Cycles and EEVEE. EEVEE selected after image and
  performance comparison: the headless studio preserves canonical geometry,
  soft shadows and the required feature detail, with practical 30-fps rendering.
- Full 240-second rough cut reviewed by Fable 5.1: FIX-FIRST, then **READY**
  after presentation fixes. Actual model metadata confirms `claude-fable-5-1`.
- Native 30-fps motion tests: 14-second periodic slide and 8-second assembly;
  both decode fully with the expected frame counts and no errors.
- **Final delivery complete:** captioned film, caption-free film, SRT, 40-second
  teaser and thumbnail under `video/output/final/`.
- Both full films: 240 seconds, 1920×1080, native 30 fps, 7,200 decoded frames.
  Teaser: 40 seconds, same resolution/rate, 1,200 decoded frames.
- `DELIVERY_CHECKS.json`: PASS on full decoding, 5,700 source PNGs, durations,
  resolution/rate, canonical/source/output hashes, subtitle layout and context labels.
- Final Fable 5.1 media review: **READY**, no blocking visible defects. Main
  model identity confirmed by returned CLI metadata. Scope and limits below.
- GPU 3 is released. Nothing was uploaded or published.

## Production corrections to the approved plan

1. Corrected cue 12 to “These copies now overlap.” The two positive pyramid
   portions meet at their base plane; each protrudes into the other solid's
   carrier. The **solids** overlap. The exact section records this correctly.
2. The periodic comparison highlights an exposed three-chair strip, buffered
   along the tested translation. A buried 27-copy motif was mathematically
   correct but invisible. Both translated surface strips are exactly contained
   in the displayed lattice. Artificial display colours also repeat along b1.
3. A cut from the flattened macro to the plain-chair hero replaces the poorly
   lit long pullback. A four-second true-geometry pair shot anchors the section.
4. Growth cameras pull back before new copies appear. Existing copies retain
   their exact world poses. The initial tile is never moved to recenter a patch.
5. Mirroring uses x/y transposition, determinant -1. This leaves the symmetric
   plain-carrier silhouette unchanged and reflects the actual feature geometry.
6. Assembly travel is translucent and labelled; settled poses use exact source
   matrices. The animation makes no collision-free physical assembly claim.

## Files and reproducibility

`captions.json` is the text/timing master. `compose.py` regenerates the SRT.
`export_scene_data.py` archives the pinned inputs, asserts all four canonical
hashes before geometry checks, and exports render-boundary floats only afterward.
`build_scene.py` uses linked copies of that canonical mesh. No bevel, displacement,
approximate contact predicate or remodeled replacement Q is used.

Large tools, source cache, individual frames and outputs are ignored below
`video/`. Distribution must use an explicit allowlist; never archive the entire
working tree, private thread, historical directories, review transcripts or tools.

Hosted app and notebook URLs are still awaiting the owner. The end card links
to the real repository, whose instructions offer the downloadable assets.

## Independent preview review, round 1

Actual CLI model metadata confirms `claude-fable-5-1`. Fable inspected the
encoded preview through all 480 decoded 2-fps samples and selected full-size
frames. It did not hear audio or watch real-time playback. Review scope was
scientific communication and visuals, not the theorem. Raw records are private
under `offgit/video_production_review/` and excluded from delivery.

FIX-FIRST repairs implemented in rough cut 3:

- Caption 7 describes the strip that actually moves; the global periodic witness
  remains recorded separately. The stale interior-motif label is removed.
- The strip uses a depth-independent projected outline with a dark backing,
  preserving the exact same projected carrier geometry throughout the slide.
- The contact section has a prominent screen-space ring and leader at the exact
  projected world point. The overlap length now says “of a unit edge”.
- Coarsening labels occupy an opaque lower-left panel and say “Scale 2/4”.
- The count is singular for one copy and remains at 4,096 after colours clear.
- Mirror labels identify the tiny features as the source of handedness.
- Magnification is explicitly uniform, and the proof diagram includes the
  clearly labelled numerical illustration 4 → 2 → 1 → 1/2.
- Bright macro shots have an opaque header backing for the essential labels.

Intentional static holds: the periodic 3D background is fixed after 0:40 while
its projected outline animates at native 30 fps. The universal-claim view is
fixed from 2:26 to 2:40. These exact unchanged backgrounds are reused, without
motion interpolation. All other moving 3D shots render every final frame.

The final camera audit passes all 42 editorial checkpoints. The independent
Blender/projected-overlay comparison differs by at most 0.001622 pixels (a
graphics alignment tolerance, never used to decide geometric validity).

## Preview closure — READY

Fable 5.1 returned READY after inspecting all 20 revised decoded-frame sheets
and the requested full-size keys. Actual model metadata again confirms
`claude-fable-5-1`. The full 1080p/30-fps render is now authorized by the already
approved production plan and is starting on GPU 3.

Its three non-blocking polish notes were applied: dark backing for the copy
counter, 128 samples during translucent assembly (64 in other final shots),
and removal of the redundant depth-tested section leader. These changes do
not change mathematical geometry, poses or captions.

## Final media review and handoff

The fresh final Fable 5.1 review inspected all 20 full-film sheets (480 decoded
samples), 140 slide samples and 80 assembly samples at 10 fps, all 80 teaser
samples, the thumbnail and selected full-resolution keys from the actual
encoded media. Verdict: **READY**, with no blocking visible defect. It confirmed
that the two shapes and the universal claim are distinguished, one failed
arrangement is not presented as the proof, local recurrence and colour are
explained, and coarsening/handedness/finite symmetry are labelled accurately.

Its remaining notes were cosmetic: early explanatory headings, buffered-layer
slivers, disclosed ghost travel, and fast camera pullbacks. They do not change
the delivery verdict. The reviewer did not watch real-time playback or assess
audio, and this is not a theorem verdict. Full technical decoding separately
covered all delivered frames. The procedural audio is un-clipped and has a
quiet final gain; no third-party recording is included.

The final source pin is copied to `video/source_pin.json`. Regenerating from
that independent pin produced byte-identical scene data and exact-check
receipts, so later reader-package pin changes cannot silently alter this film.
The final source/asset manifest is `video/output/final/manifest.json`.

Use `r44_captioned.mp4` for ordinary viewing and `r44_clean.mp4` with `r44.srt`
for captions supplied by the player. The 40-second teaser and thumbnail are
ready alongside them. `DESCRIPTION.md` supplies publication text and chapters.
Hosted app/notebook links still await the owner; the end card uses the real
repository URL. All production tasks in the approved local scope are complete.
