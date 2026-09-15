# viewer/ — Chair44 (R44) in your browser

Open `index.html` (double-click; no server, no network). Rotate with the mouse, zoom with the
wheel, right-drag or shift-drag to pan, pinch on touch.

| Control | What it does |
|---|---|
| View | one tile, the eight-child cluster, or the 64-, 512- and 4096-copy patches (the substitution applied 2, 3 or 4 times) |
| Look | Feature map (default): the exact solid with source-derived filled coral squares for bumps and hollow sky squares for dents; Exact: canonical geometry with no enlargement; Schematic: the real square-pyramid pattern drawn with bases ×5 and heights ×80, with a checkbox (or E) returning it to true scale |
| Outline the feature bases | in Schematic mode, outlines the square-pyramid bases (coral = bump, sky = dent) |
| Colour | bump/dent, height class (12 heights), copy (child, parent or grandparent), or plain |
| Period test | on the 64, 512 and cousin views: displace every copy by an integer vector and colour local same-frame matches green, mismatches red; a whole-space period would make every tested comparison green, and 100% on a finite window proves nothing |
| Periodic cousin | the same chair with its features flattened, tiling by lattice translations: "Try a true period" turns every tested copy green |
| Coarsen | replaces each eight-copy parent by the fresh standardized copy the coarsening uses, drawn 2× larger per level |
| Explode copies | separates the copies so the rotations are visible |

The page is generated from the canonical rational source data, converted to display floats, with source hashes recorded: `build_data.py` embeds `solid/r44_solid.json` and the
44-contact atlas from `certificates/candidate_certificate.json` into `r44_data.js` (with the
source hashes). Regenerate after any change to those files:

```sh
python3 viewer/build_data.py
```

Nothing here is evidence for the theorem. The feature-map symbols and colours are annotations;
the tile is one plain, unmarked solid. Schematic mode is explicitly enlarged and is not the
theorem's solid.
`vendor/three.min.js` is three.js r128 (MIT, `vendor/THREE_LICENSE`). `design_inspiration.png` is
the palette reference the page follows.
