#!/usr/bin/env python3
"""Render presentation figures of the R44 solid straight from the canonical data.

    python3 figures/render_r44.py            # writes figures/*.png
    python3 figures/render_r44.py --size 1400 --out figures

Dependencies: numpy and Pillow only (no OpenGL). Geometry comes from
solid/r44_solid.json (exact rational mesh) and, for the multi-tile figures, from
the child poses in simulations/patches.py. Nothing here is verification: the
figures are pictures of the object the theorem is about.

Figures
  r44_tile.png            the solid, true proportions; feature squares coloured by polarity
  r44_panel_features.png  one exposed panel with its eight square pyramids, heights
                          exaggerated (stated on the image) so the polarity pattern is visible
  r44_parent_cluster.png  the eight-child dissection: eight rotated copies forming 2P
  r44_patch64.png         two refinements: 64 copies, coloured by parent
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw, ImageFilter, ImageFont

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "simulations"))
import patches as sim_patches  # noqa: E402  (canonical child poses)

# ----------------------------------------------------------------------------- data


def load_solid():
    solid = json.loads((ROOT / "solid" / "r44_solid.json").read_text())
    verts = np.array([[float(Fraction(c)) for c in v] for v in solid["vertices"]])
    tris = np.array(solid["triangles"], dtype=np.int64)
    apex_sign = {}
    for patch in solid["patches"]:
        apex = tuple(float(Fraction(c)) for c in patch["apex"])
        apex_sign[apex] = 1 if patch["coefficient"] > 0 else -1
    vertex_sign = np.zeros(len(verts), dtype=np.int64)
    lookup = {tuple(np.round(v, 9)): i for i, v in enumerate(verts)}
    for apex, sign in apex_sign.items():
        vertex_sign[lookup[tuple(np.round(np.array(apex), 9))]] = sign
    # A triangle is a feature face iff its normal is not axis parallel; its polarity is the apex's.
    n = np.cross(verts[tris[:, 1]] - verts[tris[:, 0]], verts[tris[:, 2]] - verts[tris[:, 0]])
    n /= np.linalg.norm(n, axis=1, keepdims=True)
    axis_aligned = (np.abs(n) > 1 - 1e-9).any(axis=1)
    tri_sign = np.zeros(len(tris), dtype=np.int64)
    for k in np.where(~axis_aligned)[0]:
        s = vertex_sign[tris[k]]
        tri_sign[k] = s[s != 0][0] if (s != 0).any() else 0
    return solid, verts, tris, tri_sign


def chair_mesh():
    """48 triangles: the exposed unit panels of the seven-cube chair (no features)."""
    cells = [(x, y, z) for x in (0, 1) for y in (0, 1) for z in (0, 1) if (x, y, z) != (1, 1, 1)]
    cellset = set(cells)
    verts, tris, index = [], [], {}
    for c in cells:
        for axis in range(3):
            for side in (0, 1):
                nb = list(c)
                nb[axis] += 1 if side else -1
                if tuple(nb) in cellset:
                    continue
                u, v = [a for a in range(3) if a != axis]
                base = np.array(c, dtype=float)
                base[axis] += side
                quad = []
                for du, dv in ((0, 0), (1, 0), (1, 1), (0, 1)):
                    p = base.copy()
                    p[u] += du
                    p[v] += dv
                    quad.append(p)
                centre = np.array(c, dtype=float) + 0.5
                nrm = np.cross(quad[1] - quad[0], quad[2] - quad[0])
                if nrm @ (quad[0] - centre) < 0:  # orient outward
                    quad = quad[::-1]
                idx = []
                for p in quad:
                    key = tuple(int(round(c)) for c in p)
                    if key not in index:
                        index[key] = len(verts)
                        verts.append(p)
                    idx.append(index[key])
                tris.append((idx[0], idx[1], idx[2]))
                tris.append((idx[0], idx[2], idx[3]))
    return np.array(verts), np.array(tris, dtype=np.int64)


def apply_pose(points, pose):
    (perm, signs), t = pose
    out = np.empty_like(points)
    for i in range(3):
        out[:, i] = signs[i] * points[:, perm[i]] + t[i]
    return out


# ----------------------------------------------------------------------------- camera / raster


class Camera:
    def __init__(self, eye, target, fov_deg, width, height, up=(0, 0, 1)):
        self.eye = np.array(eye, float)
        f = np.array(target, float) - self.eye
        f /= np.linalg.norm(f)
        r = np.cross(f, np.array(up, float))
        r /= np.linalg.norm(r)
        u = np.cross(r, f)
        self.basis = np.stack([r, u, f])  # rows: right, up, forward
        self.focal = 0.5 * height / np.tan(np.radians(fov_deg) / 2)
        self.w, self.h = width, height

    def project(self, pts):
        rel = (pts - self.eye) @ self.basis.T
        depth = rel[:, 2]
        sx = self.w / 2 + self.focal * rel[:, 0] / depth
        sy = self.h / 2 - self.focal * rel[:, 1] / depth
        return np.stack([sx, sy], axis=1), depth


def shade(normals, base_rgb, cam, lights, two_sided=False):
    """Flat shading: ambient + Lambert + Blinn specular for each light (dir, colour, power)."""
    view = cam.basis[2]
    col = base_rgb * 0.22
    for ldir, lcol, spec in lights:
        l = np.array(ldir, float)
        l /= np.linalg.norm(l)
        nl = normals @ l
        diff = (np.abs(nl) if two_sided else np.clip(nl, 0, None))[:, None]
        h = l - view
        h /= np.linalg.norm(h)
        sp = np.clip(normals @ h, 0, None)[:, None] ** 48
        col = col + base_rgb * diff * np.array(lcol) * 0.8 + sp * spec * np.array(lcol)
    return np.clip(col, 0, 1)


def rasterize(tris_xyz, colors, cam, zbuf, img):
    """Painter-free z-buffer fill of flat-coloured triangles (screen-space barycentrics)."""
    n = len(tris_xyz)
    flat = tris_xyz.reshape(-1, 3)
    scr, depth = cam.project(flat)
    scr = scr.reshape(n, 3, 2)
    depth = depth.reshape(n, 3)
    H, W = zbuf.shape
    for k in range(n):
        p = scr[k]
        x0, y0 = np.floor(p[:, 0].min()), np.floor(p[:, 1].min())
        x1, y1 = np.ceil(p[:, 0].max()), np.ceil(p[:, 1].max())
        if x1 < 0 or y1 < 0 or x0 >= W or y0 >= H:
            continue
        x0, y0 = int(max(x0, 0)), int(max(y0, 0))
        x1, y1 = int(min(x1, W - 1)), int(min(y1, H - 1))
        if x1 < x0 or y1 < y0:
            continue
        xs = np.arange(x0, x1 + 1) + 0.5
        ys = np.arange(y0, y1 + 1) + 0.5
        X, Y = np.meshgrid(xs, ys)
        (ax, ay), (bx, by), (cx, cy) = p
        area = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
        if abs(area) < 1e-12:
            continue
        w0 = ((bx - X) * (cy - Y) - (by - Y) * (cx - X)) / area
        w1 = ((cx - X) * (ay - Y) - (cy - Y) * (ax - X)) / area
        w2 = 1 - w0 - w1
        inside = (w0 >= -1e-9) & (w1 >= -1e-9) & (w2 >= -1e-9)
        if not inside.any():
            continue
        z = w0 * depth[k, 0] + w1 * depth[k, 1] + w2 * depth[k, 2]
        sub = zbuf[y0:y1 + 1, x0:x1 + 1]
        mask = inside & (z < sub)
        sub[mask] = z[mask]
        img[y0:y1 + 1, x0:x1 + 1][mask] = colors[k]


def draw_edges(segments, cam, zbuf, img, color, width_px, bias=2e-3):
    """Depth-tested polyline samples (used for crease edges)."""
    H, W = zbuf.shape
    a, b = segments[:, 0], segments[:, 1]
    sa, da = cam.project(a)
    sb, db = cam.project(b)
    length = np.linalg.norm(sb - sa, axis=1)
    for i in range(len(segments)):
        n = int(max(2, np.ceil(length[i] / 0.6)))
        t = np.linspace(0, 1, n)[:, None]
        pts = sa[i] + t * (sb[i] - sa[i])
        z = da[i] + t[:, 0] * (db[i] - da[i])
        r = width_px / 2
        for dx in np.arange(-r, r + 0.01, 0.5):
            for dy in np.arange(-r, r + 0.01, 0.5):
                if dx * dx + dy * dy > r * r + 0.25:
                    continue
                x = np.round(pts[:, 0] + dx).astype(int)
                y = np.round(pts[:, 1] + dy).astype(int)
                ok = (x >= 0) & (x < W) & (y >= 0) & (y < H)
                x, y, zz = x[ok], y[ok], z[ok]
                vis = zz <= zbuf[y, x] * (1 + bias)
                img[y[vis], x[vis]] = color


def crease_segments(verts, tris, min_angle=1e-6):
    """Edges whose two incident faces are not coplanar."""
    n = np.cross(verts[tris[:, 1]] - verts[tris[:, 0]], verts[tris[:, 2]] - verts[tris[:, 0]])
    n /= np.linalg.norm(n, axis=1, keepdims=True)
    edge_faces = {}
    for k, (a, b, c) in enumerate(tris):
        for e in ((a, b), (b, c), (c, a)):
            edge_faces.setdefault(tuple(sorted(e)), []).append(k)
    segs = []
    for (a, b), faces in edge_faces.items():
        if len(faces) == 2 and 1 - abs(n[faces[0]] @ n[faces[1]]) > min_angle:
            segs.append((verts[a], verts[b]))
    return np.array(segs)


def background(W, H, top=(0.055, 0.075, 0.12), bottom=(0.16, 0.19, 0.26)):
    y = np.linspace(0, 1, H)[:, None, None]
    img = np.array(top) * (1 - y) + np.array(bottom) * y
    img = np.broadcast_to(img, (H, W, 3)).copy()
    yy, xx = np.mgrid[0:H, 0:W]
    r = np.sqrt(((xx - W / 2) / W) ** 2 + ((yy - H * 0.55) / H) ** 2)
    img *= (1 - 0.55 * np.clip(r - 0.25, 0, 1))[:, :, None]
    return img


def ground_shadow(tris_xyz, light_dir, floor_z, cam, W, H, strength=0.55, blur=18):
    """Project the mesh along the light onto the floor plane and darken the backdrop there."""
    l = np.array(light_dir, float)
    l /= np.linalg.norm(l)
    flat = tris_xyz.reshape(-1, 3)
    t = (flat[:, 2] - floor_z) / l[2]
    proj = flat - t[:, None] * l
    scr, _ = cam.project(proj)
    mask = Image.new("L", (W, H), 0)
    d = ImageDraw.Draw(mask)
    scr = scr.reshape(-1, 3, 2)
    for tri in scr:
        d.polygon([tuple(p) for p in tri], fill=255)
    mask = mask.filter(ImageFilter.GaussianBlur(blur))
    m = np.asarray(mask, dtype=float) / 255.0
    return 1 - strength * m


def render_scene(meshes, cam, lights, W, H, edge_sets=(), shadow=None):
    """meshes: list of (verts, tris, per-triangle base colours)."""
    img = background(W, H)
    if shadow is not None:
        tri_all = np.concatenate([v[t] for v, t, _ in meshes])
        img *= ground_shadow(tri_all, shadow[0], shadow[1], cam, W, H)[:, :, None]
    zbuf = np.full((H, W), np.inf)
    for verts, tris, base in meshes:
        tri_xyz = verts[tris]
        n = np.cross(tri_xyz[:, 1] - tri_xyz[:, 0], tri_xyz[:, 2] - tri_xyz[:, 0])
        n /= np.linalg.norm(n, axis=1, keepdims=True)
        # orient normals away from the camera-facing test: use the outward convention of the data
        cols = shade(n, base, cam, lights)
        rasterize(tri_xyz, cols, cam, zbuf, img)
    for segs, color, width in edge_sets:
        draw_edges(segs, cam, zbuf, img, np.array(color), width)
    return img


def finish(img, ss, caption=None, subcaption=None):
    im = Image.fromarray((np.clip(img, 0, 1) * 255).astype(np.uint8))
    im = im.resize((im.width // ss, im.height // ss), Image.LANCZOS)
    if caption:
        band = Image.new("RGBA", im.size, (0, 0, 0, 0))
        ImageDraw.Draw(band).rectangle([0, 0, im.width, int(im.width * 0.045 + im.width // 40 + im.width // 60)],
                                       fill=(8, 12, 22, 175))
        im = Image.alpha_composite(im.convert("RGBA"), band).convert("RGB")
        d = ImageDraw.Draw(im)
        try:
            font = ImageFont.truetype("DejaVuSans.ttf", max(14, im.width // 52))
            small = ImageFont.truetype("DejaVuSans.ttf", max(11, im.width // 80))
        except OSError:
            font = small = ImageFont.load_default()
        d.text((im.width * 0.04, im.height * 0.045), caption, fill=(235, 235, 240), font=font)
        if subcaption:
            d.text((im.width * 0.04, im.height * 0.045 + im.width // 40), subcaption,
                   fill=(170, 175, 190), font=small)
    return im


# ----------------------------------------------------------------------------- palettes

IVORY = np.array([0.93, 0.90, 0.83])
CORAL = np.array([0.97, 0.42, 0.22])   # protrusion
TEAL = np.array([0.20, 0.66, 0.90])    # recess
CHILD_COLORS = np.array([
    [0.95, 0.55, 0.25], [0.35, 0.70, 0.90], [0.60, 0.80, 0.35], [0.90, 0.40, 0.55],
    [0.98, 0.85, 0.35], [0.55, 0.50, 0.90], [0.35, 0.80, 0.70], [0.93, 0.90, 0.83],
])
LIGHTS = [((-0.5, -1.0, 1.4), (1.0, 0.96, 0.9), 0.35), ((1.2, 0.6, 0.5), (0.45, 0.55, 0.75), 0.05)]


def tile_colors(tri_sign):
    cols = np.tile(IVORY, (len(tri_sign), 1))
    cols[tri_sign > 0] = CORAL
    cols[tri_sign < 0] = TEAL
    return cols


# ----------------------------------------------------------------------------- figures


def fig_tile(verts, tris, tri_sign, size, ss, out):
    W = H = size * ss
    cam = Camera(eye=(6.2, -5.4, 4.6), target=(1.0, 1.0, 0.95), fov_deg=24, width=W, height=H)
    big = crease_segments(verts, tris, min_angle=0.5)  # carrier edges only (features are < 0.12 rad)
    img = render_scene([(verts, tris, tile_colors(tri_sign))], cam, LIGHTS, W, H,
                       edge_sets=[(big, (0.10, 0.09, 0.08), 1.6 * ss)],
                       shadow=((-0.5, -1.0, 1.4), 0.0))
    finish(img, ss, "R44", "seven-cube chair, 24 panels × 8 square pyramids (heights ±j/10000): coral = protrusion, teal = recess").save(out)


def fig_panel(solid, size, ss, out, exaggeration=25):
    W, H = int(size * 1.35) * ss, size * ss
    face = [p for p in solid["patches"] if p["face"] == 3]  # a panel with both polarities
    base_pts = np.array([[float(Fraction(c)) for c in q] for p in face for q in p["base"]])
    const_axis = int(np.argmin(base_pts.std(axis=0)))
    plane = base_pts[0, const_axis]
    apex0 = np.array([float(Fraction(c)) for c in face[0]["apex"]])
    normal = np.zeros(3)
    normal[const_axis] = np.sign(apex0[const_axis] - plane) * (1 if face[0]["coefficient"] > 0 else -1)
    u, v = [a for a in range(3) if a != const_axis]
    centre = np.zeros(3)
    centre[const_axis] = plane
    centre[u] = np.round(base_pts[:, u].mean() * 2) / 2
    centre[v] = np.round(base_pts[:, v].mean() * 2) / 2
    # panel plate: the unit square minus the eight base squares (so recesses are visible), as a grid
    bases = []
    for p in face:
        base = np.array([[float(Fraction(c)) for c in q] for q in p["base"]])
        bases.append((base[:, u].min(), base[:, u].max(), base[:, v].min(), base[:, v].max()))
    cuts_u = sorted({centre[u] - 0.5, centre[u] + 0.5} | {b[0] for b in bases} | {b[1] for b in bases})
    cuts_v = sorted({centre[v] - 0.5, centre[v] + 0.5} | {b[2] for b in bases} | {b[3] for b in bases})
    verts, tris, cols = [], [], []

    def add_quad(corners, colour):
        i = len(verts)
        verts.extend(corners)
        tris.extend([(i, i + 1, i + 2), (i, i + 2, i + 3)])
        cols.extend([colour, colour])

    def pt(uu, vv, depth=0.0):
        q = centre.copy()
        q[u], q[v] = uu, vv
        return q + normal * depth

    for a0, a1 in zip(cuts_u[:-1], cuts_u[1:]):
        for b0, b1 in zip(cuts_v[:-1], cuts_v[1:]):
            if any(abs(a0 - b[0]) < 1e-12 and abs(a1 - b[1]) < 1e-12 and abs(b0 - b[2]) < 1e-12 and abs(b1 - b[3]) < 1e-12 for b in bases):
                continue  # hole
            add_quad([pt(a0, b0), pt(a1, b0), pt(a1, b1), pt(a0, b1)], IVORY)
    thick = 0.08
    lo_u, hi_u, lo_v, hi_v = cuts_u[0], cuts_u[-1], cuts_v[0], cuts_v[-1]
    for (p0, p1) in (((lo_u, lo_v), (hi_u, lo_v)), ((hi_u, lo_v), (hi_u, hi_v)), ((hi_u, hi_v), (lo_u, hi_v)), ((lo_u, hi_v), (lo_u, lo_v))):
        add_quad([pt(*p0), pt(*p1), pt(*p1, -thick), pt(*p0, -thick)], IVORY * 0.8)
    for p in face:
        base = np.array([[float(Fraction(c)) for c in q] for q in p["base"]])
        apex = np.array([float(Fraction(c)) for c in p["apex"]])
        h = apex - base.mean(axis=0)
        apex_ex = base.mean(axis=0) + h * exaggeration
        sign = 1 if p["coefficient"] > 0 else -1
        col = CORAL if sign > 0 else TEAL
        i = len(verts)
        verts.extend(list(base) + [apex_ex])
        for k in range(4):
            tris.append((i + k, i + (k + 1) % 4, i + 4))
            cols.append(col * (0.8 + 0.06 * k))
    outline_segs = []
    for p in face:
        base = np.array([[float(Fraction(c)) for c in q] for q in p["base"]])
        outline_segs += [(base[k], base[(k + 1) % 4]) for k in range(4)]
    verts = np.array(verts)
    tris = np.array(tris)
    cols = np.array(cols)
    eye = centre + normal * 0.70 + np.eye(3)[u] * 0.26 - np.eye(3)[v] * 0.20
    up = np.eye(3)[v] if const_axis != 2 else np.eye(3)[u]
    cam = Camera(eye=eye, target=centre, fov_deg=48, width=W, height=H, up=up)
    lights = [(tuple(normal * 1.2 + np.eye(3)[u] * 0.6 - np.eye(3)[v] * 0.8), (1.0, 0.96, 0.9), 0.3),
              (tuple(normal * 0.4 - np.eye(3)[u]), (0.4, 0.5, 0.7), 0.05)]
    n = np.cross(verts[tris[:, 1]] - verts[tris[:, 0]], verts[tris[:, 2]] - verts[tris[:, 0]])
    n /= np.linalg.norm(n, axis=1, keepdims=True)
    # outward-facing normals for the slab were built by hand; ensure the pyramids' normals face the camera
    img = background(W, H)
    zbuf = np.full((H, W), np.inf)
    n = n * np.sign(n @ (cam.eye - verts[tris[:, 0]]).T.diagonal() + 1e-12)[:, None]  # face the camera
    rasterize(verts[tris], shade(n, cols, cam, lights), cam, zbuf, img)
    draw_edges(np.array(outline_segs), cam, zbuf, img, np.array([0.12, 0.10, 0.09]), 1.2 * ss)
    finish(img, ss, "One exposed panel of R44",
           f"the central part of one unit panel: eight square pyramids, base 1/50, heights ±j/10000, drawn with heights ×{exaggeration} — coral protrudes, teal recedes").save(out)


def fig_cluster(verts, tris, tri_sign, size, ss, out, explode=0.0):
    W = H = size * ss
    poses = sim_patches.sigma_depth(1)
    meshes = []
    for i, pose in enumerate(poses):
        v = apply_pose(verts, pose)
        if explode:
            c = v.mean(axis=0)
            v = v + (c - np.array([2.0, 2.0, 2.0])) * explode
        cols = np.tile(CHILD_COLORS[i], (len(tris), 1))
        cols[tri_sign > 0] = CORAL * 0.9
        cols[tri_sign < 0] = TEAL * 0.9
        meshes.append((v, tris, cols))
    cam = Camera(eye=(11.5, -10.5, 8.5), target=(1.9, 1.9, 1.7), fov_deg=26, width=W, height=H)
    edge = crease_segments(verts, tris, min_angle=0.5)
    segs = np.concatenate([np.stack([apply_pose(edge[:, 0], p), apply_pose(edge[:, 1], p)], axis=1) for p in poses])
    img = render_scene(meshes, cam, LIGHTS, W, H, edge_sets=[(segs, (0.08, 0.07, 0.07), 1.3 * ss)],
                       shadow=((-0.5, -1.0, 1.4), 0.0))
    finish(img, ss, "The eight-child dissection",
           "eight proper rotations of R44 form the doubled chair 2P; the same rule repeats at every scale").save(out)


def fig_patch(size, ss, out, depth=2):
    W = H = size * ss
    cverts, ctris = chair_mesh()
    poses = sim_patches.sigma_depth(depth)
    parents = sim_patches.sigma_depth(depth - 1)
    meshes = []
    for i, pose in enumerate(poses):
        col = CHILD_COLORS[(i // 8) % len(CHILD_COLORS)] * (0.85 + 0.15 * ((i % 8) / 7))
        meshes.append((apply_pose(cverts, pose), ctris, np.tile(col, (len(ctris), 1))))
    span = 2 ** (depth + 1)
    c = span / 2 - 0.3
    cam = Camera(eye=(c + 2.6 * span, c - 2.4 * span, c + 1.9 * span), target=(c, c, c * 0.9),
                 fov_deg=24, width=W, height=H)
    edge = crease_segments(cverts, ctris, min_angle=0.5)
    segs = np.concatenate([np.stack([apply_pose(edge[:, 0], p), apply_pose(edge[:, 1], p)], axis=1) for p in poses])
    img = render_scene(meshes, cam, LIGHTS, W, H, edge_sets=[(segs, (0.08, 0.07, 0.07), 0.9 * ss)],
                       shadow=((-0.5, -1.0, 1.4), 0.0))
    finish(img, ss, f"{len(poses)} copies after {depth} refinements",
           f"coloured by parent ({len(parents)} parents); every contact is one of the 44 registered contacts").save(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, default=ROOT / "figures")
    ap.add_argument("--size", type=int, default=1400)
    ap.add_argument("--supersample", type=int, default=2)
    ap.add_argument("--only", nargs="*", default=None, help="subset of: tile panel cluster patch")
    args = ap.parse_args(argv)
    args.out.mkdir(parents=True, exist_ok=True)
    solid, verts, tris, tri_sign = load_solid()
    todo = set(args.only or ["tile", "panel", "cluster", "patch"])
    if "tile" in todo:
        fig_tile(verts, tris, tri_sign, args.size, args.supersample, args.out / "r44_tile.png")
    if "panel" in todo:
        fig_panel(solid, args.size, args.supersample, args.out / "r44_panel_features.png")
    if "cluster" in todo:
        fig_cluster(verts, tris, tri_sign, args.size, args.supersample, args.out / "r44_parent_cluster.png")
    if "patch" in todo:
        fig_patch(args.size, args.supersample, args.out / "r44_patch64.png")
    print("wrote", ", ".join(sorted(p.name for p in args.out.glob("r44_*.png"))))


if __name__ == "__main__":
    main()
