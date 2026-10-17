#!/usr/bin/env python3
"""chair44_blender.py - build Chair44 (R44) supertiles / patches in Blender.

Same pattern as bezier_spectre_blender.py: run it with plain python and it relaunches
itself inside Blender.  Arguments:

    python3 chair44_blender.py [depth] [decorated 0|1] [exag] [color_level]

    depth        0 = one chair, 1 = 8-chair supertile, 2 = 64 chairs, 3 = 512 (default 1)
    decorated    1 = use the true 2138-vertex solid with the 192 pyramids (default 0)
    exag         feature height multiplier, only for decorated (default 1; try 300..2000)
    color_level  hierarchy digit used for colour: 0 = top-level child (default 0)

One Blender object per colour group, so large patches stay light.
Needs Blender on PATH; not exercised by the repository tests.
"""
import colorsys
import os
import subprocess
import sys

try:
    import bpy
except ImportError:
    bpy = None

HERE = os.path.dirname(os.path.abspath(__file__))
if '--' in sys.argv:
    exargs = sys.argv[sys.argv.index('--') + 1:]
else:
    exargs = sys.argv[1:] if bpy is None else []

if bpy is None and __name__ == '__main__':
    cmd = ['blender', '--python-exit-code', '1', '--python-use-system-env',
           '--python', os.path.abspath(__file__)]
    if exargs:
        cmd += ['--'] + exargs
    print(cmd)
    subprocess.check_call(cmd)
    sys.exit()

sys.path.insert(0, HERE)
import numpy as np  # noqa: E402
import chair44  # noqa: E402


def get_params():
    p = {'depth': 1, 'decorated': 0, 'exag': 1.0, 'color_level': 0}
    keys = ['depth', 'decorated', 'exag', 'color_level']
    for k, v in zip(keys, exargs):
        p[k] = float(v) if k == 'exag' else int(v)
    return p


def label_color(i, n):
    r, g, b = colorsys.hsv_to_rgb(i / max(n, 1), 0.55, 0.95)
    return (r, g, b, 1.0)


def generate(depth=1, decorated=0, exag=1.0, color_level=0):
    poses = chair44.sigma_depth(depth)
    if decorated:
        V, T = chair44.decorated_mesh(chair44.Decoration(), exag)
    else:
        V, T = chair44.base_chair_mesh()
    digits = chair44.tile_digits(depth)
    level = min(color_level, max(depth - 1, 0))
    groups = {}
    for pose, dg in zip(poses, digits):
        groups.setdefault(dg[level] if dg else 0, []).append(pose)
    objs = []
    for label in sorted(groups):
        W, TT, _ = chair44.assemble(groups[label], V, T)
        mesh = bpy.data.meshes.new('Chair44_%d' % label)
        mesh.from_pydata(W.tolist(), [], TT.tolist())
        mesh.update()
        obj = bpy.data.objects.new('Chair44_%d' % label, mesh)
        bpy.context.collection.objects.link(obj)
        mat = bpy.data.materials.new('chair44_mat_%d' % label)
        mat.diffuse_color = label_color(label, len(groups))
        obj.data.materials.append(mat)
        objs.append(obj)
    return objs


if bpy is not None:
    for o in list(bpy.data.objects):
        bpy.data.objects.remove(o, do_unlink=True)
    generate(**get_params())
