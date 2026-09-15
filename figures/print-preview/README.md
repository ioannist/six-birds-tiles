# Corrected monochrome figure previews

These previews replace the rejected AI-generated visual concept with deterministic artwork
constructed from `solid/r44_solid.json`. The manuscript includes `figure1-corrected.pdf`
and `figure3-corrected.pdf` as Figures 1 and 3, respectively.
The previous generated concept is not used in any of these files.

- `figure1-corrected.png`, `.pdf`, `.svg`: full chair with panel 13 outlined, its exact
  eight-feature plan inset, and sections through its +9 and -9 features.
- `figure3-corrected.png`, `.pdf`, `.svg`: oblique and plan views of that same panel 13.
- `all-panels-audit.pdf`: all 24 panels, showing every signed coefficient; small numbers
  identify canonical roles 0–191. The chart uses the increasing global tangent axes.
- `feature-audit.csv`: one row per feature, with its exact centre, coefficient, true
  signed height, display multipliers and source checks.
- `geometry-audit.json`: source hashes and exact rational source/display feature vertices.
- `display-mesh.npz`: the actual triangles supplied to the renderer, with feature and panel IDs.
- `mesh-readback-audit.json`: separate read-back comparison of the display mesh against
  independently reconstructed transformed canonical triangles.
- `visibility-audit.csv`: projected visible-pixel counts per feature. Hidden rear surfaces
  and occluded parts of the notch are intentionally not visible. All eight features of
  selected panel 13 contribute pixels in the chair and both detail views.

## Display convention

The seven-cube carrier and all feature centres retain their canonical coordinates.
Every feature base is widened uniformly by **5** about its centre; every signed apex
height is multiplied by **80**. No feature is added, omitted from the mesh, relocated,
assigned a different polarity, or assigned a different relative height. Thus these are
explicitly exaggerated illustrations, not true-scale renderings of Q. Plan views retain
centre locations and polarities, but do not visually encode height magnitude; the signed
coefficients provide that information. The true height is `a/10000`, and the true base
side length is `1/50`.

Panel 13 has outward normal -y, centre (3/2, 0, 3/2), and global tangent axes x,z.
Its eight roles and coefficients are:

| Role | Local index | x | z | a |
|---|---|---|---|---|
| 104 | 0 | 11/8 | 5/4 | -9 |
| 105 | 1 | 11/8 | 7/4 | -10 |
| 106 | 2 | 13/8 | 5/4 | -11 |
| 107 | 3 | 13/8 | 7/4 | -12 |
| 108 | 4 | 5/4 | 11/8 | +9 |
| 109 | 5 | 5/4 | 13/8 | +11 |
| 110 | 6 | 7/4 | 11/8 | +10 |
| 111 | 7 | 7/4 | 13/8 | +12 |

## Checks and reproduction

`build_preview.py` checks all **192** feature records with rational arithmetic against
both the canonical mesh and `solid/native_panels.csv`, including centres, panel assignment,
base corners, apex, coefficient and all four triangle memberships. It checks all 24 exposed
carrier panels, eight features per panel, non-overlapping enlarged footprints and complete
flat-panel coverage outside the eight footprint holes.

`audit_preview.py` separately reads back the display mesh and reconstructs all **768**
expected feature triangles from the canonical source using the declared multipliers.
It also checks every flat panel's plane, bounds, area and absence of triangles covering the
footprint holes, and the signed labels in the two SVG layouts. Both audits pass.

Run from this checkout:

```sh
python3 figures/print-preview/build_preview.py
python3 figures/print-preview/audit_preview.py
```

Dependencies: the existing figure renderer, numpy, Pillow and CairoSVG. Geometry is rendered
with an orthographic camera and a depth buffer. SVG/PDF outputs contain high-resolution
raster geometry with vector typography and leader lines; they are not wholly vector meshes.
The PNG previews were also inspected at approximately 5.25 inches wide and 150 dpi.

The manuscript's figure includes and captions were updated to use these illustrations.
No theorem, canonical geometry, existing renderer, viewer or verification source has been
changed by this artwork update. These audits concern the illustration's correspondence to the source;
they make no new mathematical claim about the exaggerated display solid.
