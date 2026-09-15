# Chair44 media assets

The production campaign is complete. Every Chair44 solid and every tile
placement is rendered programmatically from the pinned canonical geometry.
Colours, feature-map glyphs, labels and backgrounds are explanatory layers.

## Finished assets

| Family | Main outputs |
|---|---|
| Reconstruction plate | `output/reconstruction/` — A1 SVG/PDF, 9,933×7,016 master and 4,000 px web copy |
| Public infographic | `output/infographic/` — portrait and wide PNG/PDF |
| Discovery hero | `output/hero/` — GitHub, Open Graph, landscape, square, portrait and story crops |
| Periodic comparison | `output/comparison/` — landscape and portrait |
| Hierarchical growth | `output/growth/` — landscape and portrait |
| Period argument | `output/period_argument/` — square and portrait |
| Verify it yourself | `output/verify/` — link preview and portrait |
| Four-card carousel | `output/carousel/` — four publication cards and a contact sheet |
| Press kit | `output/press/` — copy-space heroes, slides, A4 image, twelve transparent views and press copy |

Each family has a JSON receipt recording its pinned source commit, relevant
input hashes and output hashes. The rejected table-based reconstruction plate
was removed; the published plate marks every feature directly on six face-on
views.

The public Git repository keeps one compact representative from each main web
family, the reconstruction SVG/web plate, and their receipts. Alternate crops,
print masters, carousel and press-kit images remain local and may be distributed
as a separately checksummed release asset. The ignore rules in `media/.gitignore`
record the exact boundary; they do not delete the local production files.

## Rebuild

Use the repository Python for the standard campaign files:

```sh
python3 media/build_assets.py hero
python3 media/build_assets.py comparison
python3 media/build_assets.py growth
python3 media/build_assets.py infographic
python3 media/build_period_diagram.py
python3 media/build_carousel.py
```

The reconstruction plate, verification card and press kit use the small local
media environment for SVG/PDF or QR support:

```sh
media/.venv/bin/python media/build_plate.py
media/.venv/bin/python media/build_verify_card.py
media/.venv/bin/python media/build_press_kit.py
```

`media/.venv/` is ignored. Its required packages are Pillow, CairoSVG and
qrcode. Blender source renders are built headlessly through
`video/build_scene.py`; GPU selection is controlled by `CUDA_VISIBLE_DEVICES`.

## Geometry and display convention

The transparent exact tile source is `source/000090.png`; the annotated source
is `source/feature_map/000090.png`. The feature map puts a filled coral square
over every bump base and a hollow sky square over every dent base. These flat,
enlarged glyphs are annotations over the exact solid. They are never substitute
geometry.

At cluster scale the true features can become smaller than one pixel. Such
images either retain an explicit feature-map layer or say that the exact mesh
is present while its features are subpixel. The selected physical dimensions
are a convenient realization; matching complementary features and their
encoded profile drive the construction.

All public campaign images carry:

> Ioannis Tsiokos · with ChatGPT Astra + Six Birds Theory · EmergenceCalculus.com/r44

Pure transparent cutouts preserve reusability and store that credit, the pinned
commit and the canonical solid hash in PNG metadata. `output/press/PRESS_COPY.md`
contains the reusable caption, descriptions, credit and alt text.

## Decorative background provenance

`backgrounds/editorial_navy_v1.png` was generated with OpenAI image generation
as a decorative, non-mathematical plate. The quieter wide assets instead use a
deterministic navy gradient. The generated background prompt is recorded in
`VISUAL_DIRECTION.md`; it contains no tile geometry or factual lettering.

The ratified inventory and production rules are in
`IMAGE_ASSET_INVENTORY.md`. The visual conventions and small-format checks are
in `VISUAL_DIRECTION.md`.
