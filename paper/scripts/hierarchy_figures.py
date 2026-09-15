#!/usr/bin/env python3
"""Print illustrations of the exact carrier partitions 2P and 4P.

Orthographic vector faces, with hidden faces removed and only tile boundaries
drawn (no unit-cube grid). Features are deliberately omitted, as captioned.
"""
import sys
from pathlib import Path

import cairosvg

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "simulations"))
from patches import evidence, sigma_depth
from r44 import pose_cells

COLORS = ("#729dbb", "#d9ad69", "#91b9a1", "#bd94ac",
          "#b4aece", "#d9937c", "#8abcc1", "#c5bf88")


def render(depth, name):
    children, _, _ = evidence()
    poses = sigma_depth(depth, children)
    cells = {}
    for owner, pose in enumerate(poses):
        for cell in pose_cells(pose):
            assert cell not in cells, "overlapping carrier cells"
            cells[cell] = owner
    span = 2 ** (depth + 1)
    expected = {(x, y, z) for x in range(span) for y in range(span)
                for z in range(span)
                if min(x, y, z) < span // 2}
    assert set(cells) == expected and len(cells) == 7 * 8 ** depth
    # From the positive octant all three reentrant notch panels are visible.
    # Only outward +axis faces can face this orthographic camera.
    faces = {}
    for cell, owner in cells.items():
        for axis in range(3):
            nb = list(cell)
            nb[axis] += 1
            if tuple(nb) not in cells:
                faces[(cell, axis)] = owner

    def project(p):
        x, y, z = (v / span for v in p)
        return (360 + 320 * (x - y), 55 + 320 * (.5 * (x + y) - z + 1))

    parts = ['<rect width="720" height="750" fill="white"/>']
    edges = []
    for (cell, axis), owner in sorted(faces.items(), key=lambda f: sum(f[0][0])):
        u, v = [a for a in range(3) if a != axis]
        corners = []
        for du, dv in ((0, 0), (1, 0), (1, 1), (0, 1)):
            p = list(cell)
            p[axis] += 1
            p[u] += du
            p[v] += dv
            corners.append(project(p))
        base = COLORS[owner // (8 ** (depth - 1))]
        shade = (0.83, 0.94, 1.08)[axis]
        rgb = [min(255, round(int(base[i:i+2], 16) * shade)) for i in (1, 3, 5)]
        color = '#' + ''.join(f'{c:02x}' for c in rgb)
        points = ' '.join(f'{x:.3f},{y:.3f}' for x, y in corners)
        # Tiny same-colour stroke prevents PDF viewer hairlines between coplanar cells.
        parts.append(f'<polygon points="{points}" fill="{color}" stroke="{color}" stroke-width="1.2"/>')
        for k, (a, sign) in enumerate(((v, -1), (u, 1), (v, 1), (u, -1))):
            nb = list(cell)
            nb[a] += sign
            neighbor = faces.get((tuple(nb), axis))
            if neighbor == owner:
                continue
            x1, y1 = corners[k]
            x2, y2 = corners[(k + 1) % 4]
            parent_boundary = neighbor is None or neighbor // (8 ** (depth - 1)) != owner // (8 ** (depth - 1))
            width = 1.5 if parent_boundary else 0.75
            edges.append(f'<path d="M{x1:.3f},{y1:.3f} L{x2:.3f},{y2:.3f}" '
                         f'fill="none" stroke="#37434b" stroke-width="{width}" stroke-linecap="round"/>')
    parts.extend(edges)
    svg = '<svg xmlns="http://www.w3.org/2000/svg" width="720" height="750" viewBox="0 0 720 750">' + ''.join(parts) + '</svg>'
    out = ROOT / "figures"
    (out / f'{name}.svg').write_text(svg)
    cairosvg.svg2pdf(bytestring=svg.encode(), write_to=str(out / f'{name}.pdf'))
    cairosvg.svg2png(bytestring=svg.encode(), write_to=str(out / f'{name}.png'), output_width=1440, output_height=1500)
    print(f'{name}: {len(poses)} chairs, {len(cells)} exact cells, partition checked')


if __name__ == '__main__':
    render(1, 'r44_parent_cluster')
    render(2, 'r44_patch64')
