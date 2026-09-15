"""Shared exact integer geometry for the R44 simulation tools.

This module is deliberately small and standard-library only.  Poses use the
same JSON representation as ``candidate_certificate.json``::

    [[[permutation], [signs]], [integer translation]]

Frames act on column vectors by ``(g x)_i = signs[i] * x[perm[i]]``.
"""

from __future__ import annotations

import json
from pathlib import Path


SIMULATIONS = Path(__file__).resolve().parent
REPOSITORY = SIMULATIONS.parent
IDENTITY_FRAME = ((0, 1, 2), (1, 1, 1))
ROOT_POSE = (IDENTITY_FRAME, (0, 0, 0))
CHAIR_CELLS = frozenset(
    (x, y, z)
    for x in (0, 1)
    for y in (0, 1)
    for z in (0, 1)
    if (x, y, z) != (1, 1, 1)
)


def vector_add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def vector_subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


def vector_scale(n, a):
    return tuple(n * x for x in a)


def frame_apply(frame, vector):
    permutation, signs = frame
    return tuple(signs[i] * vector[permutation[i]] for i in range(3))


def frame_multiply(left, right):
    """Return the frame for ``left(right(x))``."""
    p, s = left
    q, t = right
    return (
        tuple(q[p[i]] for i in range(3)),
        tuple(s[i] * t[p[i]] for i in range(3)),
    )


def frame_inverse(frame):
    permutation, signs = frame
    inverse_permutation = tuple(permutation.index(i) for i in range(3))
    inverse_signs = tuple(signs[inverse_permutation[i]] for i in range(3))
    return inverse_permutation, inverse_signs


def frame_determinant(frame):
    permutation, signs = frame
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(3)
        for j in range(i + 1, 3)
    )
    return (-1 if inversions % 2 else 1) * signs[0] * signs[1] * signs[2]


def pose_multiply(left, right):
    """Return the affine pose for ``left(right(x))``."""
    g, t = left
    h, u = right
    return frame_multiply(g, h), vector_add(t, frame_apply(g, u))


def relative_pose(root, other):
    """Express ``other`` in native coordinates of ``root``."""
    g, t = root
    h, u = other
    inverse = frame_inverse(g)
    return frame_multiply(inverse, h), frame_apply(inverse, vector_subtract(u, t))


def translate_pose(pose, offset):
    frame, translation = pose
    return frame, vector_add(translation, offset)


def parse_pose(value):
    frame, translation = value
    permutation, signs = frame
    return (
        (tuple(int(x) for x in permutation), tuple(int(x) for x in signs)),
        tuple(int(x) for x in translation),
    )


def pose_json(pose):
    frame, translation = pose
    permutation, signs = frame
    return [[list(permutation), list(signs)], list(translation)]


def load_json(relative_path):
    with (REPOSITORY / relative_path).open(encoding="utf-8") as handle:
        return json.load(handle)


def cell_transform(frame, cell):
    """Transform the lower corner of a closed unit cell by a signed frame."""
    _, signs = frame
    transformed = frame_apply(frame, cell)
    return tuple(transformed[i] - (1 if signs[i] < 0 else 0) for i in range(3))


def pose_cells(pose, native_cells=CHAIR_CELLS):
    frame, translation = pose
    return frozenset(
        vector_add(cell_transform(frame, cell), translation)
        for cell in native_cells
    )


def exposed_faces(pose):
    """Map each exposed cell face key to its outward sign.

    The key is ``(axis, doubled_face_center)`` and therefore stays integral.
    """
    cells = pose_cells(pose)
    result = {}
    for cell in cells:
        for axis in range(3):
            for side in (-1, 1):
                neighbor = list(cell)
                neighbor[axis] += side
                if tuple(neighbor) in cells:
                    continue
                center = [2 * coordinate + 1 for coordinate in cell]
                center[axis] += side
                result[(axis, tuple(center))] = side
    return result


def face_adjacent(first, second):
    left = exposed_faces(first)
    right = exposed_faces(second)
    return any(left[key] == -right[key] for key in left.keys() & right.keys())

