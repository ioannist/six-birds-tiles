# figures/ — pictures of Chair44 (R44)

Rendered from the canonical data by `render_r44.py` (numpy + Pillow software rasterizer;
no OpenGL, no external assets). Regenerate with:

```sh
python3 figures/render_r44.py --only tile panel
python3 paper/scripts/hierarchy_figures.py  # print versions of Figures 6 and 7
```

| File | What it shows |
|---|---|
| `r44_tile.png` | the solid at true proportions from `solid/r44_solid.json`; the 192 feature squares coloured by polarity (coral = protrusion, teal = recess) |
| `r44_panel_features.png` | the central part of one exposed unit panel with its eight square pyramids; heights are drawn ×25 (stated on the image) so the polarity pattern is visible, bases are true size (1/50) |
| `r44_parent_cluster.png` | the eight-child carrier dissection of 2P, with small features omitted (exact poses from `simulations/patches.py`) |
| `r44_patch64.png` | two refinements: 64 copies coloured by parent; chair outlines only, features omitted at this scale |

The hierarchy generator uses CairoSVG and produces matching PDF, SVG and PNG files on a
white background without embedded text. The paper and arXiv package use the vector PDFs.
It checks the exact carrier partitions (56 and 448 unit cells); this is a figure check,
not verification of the monotile theorem. Colours annotate children or parents, and
small geometric features are omitted as stated in the captions. The legacy rasterizer
can still generate presentation versions with `--only cluster patch`; rerun the hierarchy
generator afterwards to restore the print PNGs.
