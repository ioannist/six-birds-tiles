# Chair44 (R44) — One shape. No periodic tiling.

A 4:06 3D film: meet the actual tile, compare it with a nearly identical
chair that repeats, watch compatible copies grow into space, and follow the
paper's reason that **every** R44 tiling has no nonzero translation period.

**Revision 2 delivery complete:** Chair44 titles, author and project credits,
website, and a twelve-second closing card. Both full movies are 1080p / 30 fps
/ 4:06. Full video/audio decoding, layout and digest checks pass. The revised
media received local visual review; Fable 5.1 reviewed the previous 4:00 version.
See [PRODUCTION.md](PRODUCTION.md).

Generated files are in `video/output/final/` (large media are excluded from Git):

| File | Use |
|---|---|
| `r44_captioned.mp4` | Main film, with the complete caption script. |
| `r44_clean.mp4` | Main film without the lower captions; essential scene labels remain. |
| `r44.srt` | Subtitle sidecar for the clean film. |
| `r44_teaser_40s.mp4` | A 40-second introduction cut from the finished shots. |
| `thumbnail.jpg` | 1920×1080 cover image. |
| `manifest.json` | Asset sizes/hashes, source pin and production-source hashes. |

The selected final movies, subtitle, teaser, thumbnail and manifest belong in
the corresponding GitHub or Zenodo release. Raw frames, audio intermediates,
logs and duplicate revisions remain local.

Production status and corrections: [PRODUCTION.md](PRODUCTION.md).
Approved story and captions: [VIDEO_PLAN.md](VIDEO_PLAN.md).
Exact finite checks: [DATA_CHECKS.json](DATA_CHECKS.json).
The film keeps its own immutable input reference in [source_pin.json](source_pin.json),
so later reader-package updates do not silently change a rebuild of this film.

## Build locally, without opening Blender

Run from the repository root. The production installation lives inside this
directory; no system Python or other GPU workload is changed.

```bash
python3 video/bootstrap.py
video/.venv/bin/python video/export_scene_data.py
video/.venv/bin/python video/render.py --quality preview
video/.venv/bin/python video/compose.py --quality preview
```

The preview samples motion at 2 fps, retaining the complete 246-second timeline.
After preview review, render every frame at native 1080p / 30 fps:

```bash
video/.venv/bin/python video/render.py --quality final
video/.venv/bin/python video/compose.py --quality final
video/.venv/bin/python video/compose.py --quality final --clean
```

Outputs are under `video/output/preview/` and `video/output/final/`.
`r44_captioned.mp4` includes the main captions; `r44_clean.mp4` retains all
essential explanatory labels but omits the main captions. Pair the latter with
[CAPTIONS.srt](CAPTIONS.srt). Both include a quiet original procedural music bed.
The film is fully understandable muted.

Unchanged backgrounds in the periodic
comparison and universal-claim reading hold are reused exactly; moving outlines
and captions are composed at 30 fps. No motion interpolation is used.

The renderer resumes completed PNG frames. To regenerate a changed shot,
remove that shot's **generated** frame interval first; do not reuse stale frames
after editing geometry, camera or materials. `--shots hero assembly` restricts
rendering, and `--frames 90 3600` renders selected diagnostic frames.

The default is GPU 3. `R44_VIDEO_GPU` selects a different CUDA device; verify
Blender's actual graphics process with `nvidia-smi`, especially for EEVEE.
Tools, caches, frames and movies are intentionally excluded from Git.

The movie illustrates the repository's construction and proof submission.
Finite animation is not a proof of a universal negative. Source quotations and
the exact claim-to-scene mapping belong in `EVIDENCE.md`; no new theorem is
claimed by this production pipeline.

## Finish and check a delivery

```bash
video/.venv/bin/python video/deliver.py
video/.venv/bin/python video/check_delivery.py
```

The delivery checker decodes all 7,380 frames of each full film and all 1,200
teaser frames, checks duration/resolution, verifies source images, subtitle
layout and output hashes. It is a technical check, separate from visual review.

For a motion proof of concept:

```bash
video/.venv/bin/python video/render.py --quality final --time-range 44 58
video/.venv/bin/python video/compose.py --quality final --time-range 44 58 --output-name periodic_poc.mp4
```

`review_frames.py MOVIE OUTPUT_DIR` decodes timestamped review sheets from the
actual encoded movie. `audit_scene.py` and `audit_framing.py` run inside Blender
and record pose/motion and display-framing checks respectively.

Source quotations and display conventions: [EVIDENCE.md](EVIDENCE.md).
Publication description: [DESCRIPTION.md](DESCRIPTION.md). The app and notebook
hosted URLs can be added when available; the film's end card displays the author's destination,
`www.EmergenceCalculus.com/r44`. No assets have been uploaded or published by this build.
