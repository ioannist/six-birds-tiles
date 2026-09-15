#!/usr/bin/env python3
"""Render an R44 OBJ to PNG with feature polarity colors.

This is the only simulation tool with an optional dependency.  It imports
matplotlib (and its NumPy dependency) only after argument parsing.  OBJ groups
written by patches.py carry ``baseline``, ``positive`` and ``negative``
materials, which are rendered gray, red and blue respectively.
"""

from __future__ import annotations

import argparse
from pathlib import Path


COLORS = {
    "baseline": "#b8c2d1",
    "positive": "#df3830",
    "negative": "#295cd1",
}


def read_obj(path):
    vertices = []
    faces = []
    material = "baseline"
    with Path(path).open(encoding="utf-8") as handle:
        for raw_line in handle:
            parts = raw_line.split()
            if not parts or parts[0].startswith("#"):
                continue
            if parts[0] == "v" and len(parts) >= 4:
                vertices.append(tuple(float(value) for value in parts[1:4]))
            elif parts[0] == "usemtl" and len(parts) == 2:
                material = parts[1]
            elif parts[0] == "f" and len(parts) >= 4:
                indices = [int(value.split("/", 1)[0]) - 1 for value in parts[1:]]
                for index in range(1, len(indices) - 1):
                    faces.append(((indices[0], indices[index], indices[index + 1]), material))
    if not vertices or not faces:
        raise ValueError(f"{path} does not contain renderable OBJ vertices and faces")
    return vertices, faces


def render(obj_path, png_path, elevation=24.0, azimuth=-55.0, dpi=180):
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from mpl_toolkits.mplot3d.art3d import Poly3DCollection
    except ImportError as error:
        raise RuntimeError(
            "rendering requires matplotlib (which installs NumPy); "
            "the exact generators and checkers do not require either package"
        ) from error

    vertices, faces = read_obj(obj_path)
    figure = plt.figure(figsize=(8, 8))
    axis = figure.add_subplot(111, projection="3d")
    polygons = [[vertices[index] for index in face] for face, _ in faces]
    colors = [COLORS.get(material, "#b8c2d1") for _, material in faces]
    collection = Poly3DCollection(
        polygons,
        facecolors=colors,
        edgecolors="#26313d",
        linewidths=0.06,
        alpha=1.0,
    )
    axis.add_collection3d(collection)
    coordinates = list(zip(*vertices))
    minima = [min(values) for values in coordinates]
    maxima = [max(values) for values in coordinates]
    center = [(low + high) / 2 for low, high in zip(minima, maxima)]
    radius = max(high - low for low, high in zip(minima, maxima)) / 2
    radius = radius or 1.0
    axis.set_xlim(center[0] - radius, center[0] + radius)
    axis.set_ylim(center[1] - radius, center[1] + radius)
    axis.set_zlim(center[2] - radius, center[2] + radius)
    axis.set_box_aspect((1, 1, 1))
    axis.view_init(elev=elevation, azim=azimuth)
    axis.set_axis_off()
    figure.tight_layout(pad=0)
    png_path = Path(png_path)
    png_path.parent.mkdir(parents=True, exist_ok=True)
    figure.savefig(png_path, dpi=dpi, transparent=False, bbox_inches="tight", pad_inches=0.02)
    plt.close(figure)
    return png_path


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("obj", type=Path, help="single-tile or patch OBJ from patches.py")
    parser.add_argument("png", type=Path, help="output PNG")
    parser.add_argument("--elevation", type=float, default=24.0)
    parser.add_argument("--azimuth", type=float, default=-55.0)
    parser.add_argument("--dpi", type=int, default=180)
    args = parser.parse_args(argv)
    try:
        output = render(args.obj, args.png, args.elevation, args.azimuth, args.dpi)
    except (RuntimeError, ValueError) as error:
        parser.exit(2, f"render.py: {error}\n")
    print(f"wrote {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

