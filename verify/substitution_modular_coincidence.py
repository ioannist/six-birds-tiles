#!/usr/bin/env python3
"""Independent finite check of the R44 labelled lattice substitution.

This checker reads only the canonical JSON certificate.  It reconstructs the
24 signed-permutation frames, the eight child chairs, all 168 labels, and the
cell substitution directly with Python tuples.  It does not import, parse, or
translate the Lean implementation.  Standard library only; do not run with
``python -O``.
"""

import itertools
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CERTIFICATE = ROOT / "certificates/candidate_certificate.json"
ORIGIN = (0, 0, 0)
BITS = tuple(itertools.product(range(2), repeat=3))
CHAIR_CELLS = tuple(k for k in BITS if k != (1, 1, 1))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def scale(n, a):
    return tuple(n * x for x in a)


def frame_from_json(raw):
    return tuple(raw[0]), tuple(raw[1])


def act(frame, point):
    permutation, signs = frame
    return tuple(signs[i] * point[permutation[i]] for i in range(3))


def compose(left, right):
    """Signed-permutation composition, left after right."""
    lp, ls = left
    rp, rs = right
    return (
        tuple(rp[lp[i]] for i in range(3)),
        tuple(ls[i] * rs[lp[i]] for i in range(3)),
    )


def cell_lower(frame, origin, local_cell):
    """Lower corner of the oriented unit cell indexed by local_cell."""
    permutation, signs = frame
    return tuple(
        (local_cell[permutation[i]] if signs[i] == 1
         else -local_cell[permutation[i]] - 1) + origin[i]
        for i in range(3)
    )


def child_poses(parent_frame, children):
    return tuple(
        (compose(parent_frame, child_frame), act(parent_frame, child_origin))
        for child_frame, child_origin in children
    )


def main():
    assert sys.flags.optimize == 0, "run without -O (assertions must be enabled)"
    certificate = json.loads(CERTIFICATE.read_text())
    frames = tuple(frame_from_json(raw) for raw in certificate["orientation_group"])
    children = tuple(
        (frame_from_json(raw[0]), tuple(raw[1]))
        for raw in certificate["children"]
    )

    assert len(frames) == len(set(frames)) == 24
    assert len(children) == 8
    assert len(CHAIR_CELLS) == 7

    labels = tuple((frame, cell) for frame in frames for cell in CHAIR_CELLS)
    label_index = {label: index for index, label in enumerate(labels)}
    assert len(labels) == len(label_index) == 168

    phi = {}
    for frame in frames:
        transformed_children = child_poses(frame, children)
        owners = {}
        for child_frame, child_origin in transformed_children:
            assert child_frame in label_index_by_frame(frames)
            for child_cell in CHAIR_CELLS:
                point = cell_lower(child_frame, child_origin, child_cell)
                owners.setdefault(point, []).append((child_frame, child_cell))

        doubled_cells = {
            add(scale(2, cell_lower(frame, ORIGIN, cell)), delta)
            for cell in CHAIR_CELLS
            for delta in BITS
        }
        assert len(doubled_cells) == 56
        assert set(owners) == doubled_cells
        assert all(len(found) == 1 for found in owners.values())

        for cell in CHAIR_CELLS:
            source = cell_lower(frame, ORIGIN, cell)
            source_index = label_index[(frame, cell)]
            for delta in BITS:
                target = add(scale(2, source), delta)
                target_label, = owners[target]
                phi[source_index, delta] = label_index[target_label]

    assert len(phi) == 168 * 8

    matrix = [
        [sum(phi[j, delta] == i for delta in BITS) for j in range(168)]
        for i in range(168)
    ]
    column_sums = [sum(matrix[i][j] for i in range(168)) for j in range(168)]
    assert set(column_sums) == {8}

    successors = [set(phi[j, delta] for delta in BITS) for j in range(168)]
    reachable = [set(row) for row in successors]
    primitive_profiles = []
    least_primitive_exponent = None
    for exponent in range(1, 7):
        profile = (min(map(len, reachable)), max(map(len, reachable)))
        primitive_profiles.append((exponent, profile))
        if all(len(found) == 168 for found in reachable):
            least_primitive_exponent = exponent
            break
        reachable = [
            set().union(*(successors[label] for label in found))
            for found in reachable
        ]
    assert least_primitive_exponent == 3

    states = [(ORIGIN, frozenset(range(168)))]
    coincidence_size_profiles = []
    witness = None
    least_coincidence_depth = None
    for depth in range(1, 7):
        next_states = []
        for address, possible_labels in states:
            for delta in BITS:
                next_address = add(scale(2, address), delta)
                next_labels = frozenset(phi[label, delta] for label in possible_labels)
                next_states.append((next_address, next_labels))
        size_profile = Counter(len(found) for _, found in next_states)
        coincidence_size_profiles.append((depth, sorted(size_profile.items())))
        singleton = next(
            ((address, next(iter(found))) for address, found in next_states
             if len(found) == 1),
            None,
        )
        if singleton is not None:
            least_coincidence_depth = depth
            witness = singleton
            break
        states = next_states

    assert least_coincidence_depth == 3
    assert witness == ((0, 0, 2), 78)
    address, target_index = witness
    path = [
        tuple((coordinate >> power) & 1 for coordinate in address)
        for power in reversed(range(least_coincidence_depth))
    ]
    target_frame, target_cell = labels[target_index]
    frame_index = frames.index(target_frame)
    cell_index = CHAIR_CELLS.index(target_cell)
    assert (frame_index, cell_index) == (11, 1)

    report = {
        "status": "PASS",
        "labels": len(labels),
        "addresses_per_label": len(BITS),
        "covered_cells_per_frame": 56,
        "column_sum": 8,
        "least_primitive_exponent_N": least_primitive_exponent,
        "primitive_power_reachability_min_max": primitive_profiles,
        "least_coincidence_depth_M": least_coincidence_depth,
        "coincidence_address_a": list(address),
        "coincidence_path": [list(digit) for digit in path],
        "coincidence_label_i": target_index,
        "coincidence_label": {
            "frame_index": frame_index,
            "permutation": list(target_frame[0]),
            "signs": list(target_frame[1]),
            "cell_index": cell_index,
            "cell": list(target_cell),
        },
        "coincidence_label_set_sizes": coincidence_size_profiles,
    }
    print(json.dumps(report, sort_keys=True))


def label_index_by_frame(frames):
    return set(frames)


if __name__ == "__main__":
    main()
