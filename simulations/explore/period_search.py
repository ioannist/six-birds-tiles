#!/usr/bin/env python3
"""Bounded exploratory search for rectangular periods of registered R44 tilings.

IMPORTANT: A negative result from this bounded search is not part of the
theorem's evidence.  The theorem uses intrinsic parent recognition and period
halving, not finite-box search.  This program exhausts only axis-aligned
rectangular period lattices within the explicitly printed side/cell bounds.
"""

from __future__ import annotations

import argparse
import json
import sys
from itertools import product
from pathlib import Path

SIMULATIONS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SIMULATIONS))

from r44 import ROOT_POSE, load_json, parse_pose, pose_cells, pose_json, relative_pose, translate_pose


WARNING = "NEGATIVE RESULTS ARE NOT PART OF THE THEOREM'S EVIDENCE."


class SearchLimit(Exception):
    pass


def _residue(cell, dimensions):
    return tuple(cell[axis] % dimensions[axis] for axis in range(3))


def _linear(cell, dimensions):
    x, y, z = cell
    _, height, depth = dimensions
    return (x * height + y) * depth + z


def _candidate(frame, translation, dimensions):
    pose = (frame, translation)
    cells = tuple(pose_cells(pose))
    residues = tuple(_residue(cell, dimensions) for cell in cells)
    if len(set(residues)) != 7:
        return None
    canonical = {residue: cell for residue, cell in zip(residues, cells)}
    mask = sum(1 << _linear(residue, dimensions) for residue in residues)
    return {"pose": pose, "canonical": canonical, "mask": mask}


def _face_compatible(left, left_cell, right, right_cell, step, legal):
    right_shift = tuple(left_cell[axis] + step[axis] - right_cell[axis] for axis in range(3))
    if left is right and right_shift == (0, 0, 0):
        return True
    shifted_right = translate_pose(right["pose"], right_shift)
    return relative_pose(left["pose"], shifted_right) in legal


def search_box(dimensions, frames, legal, node_limit=0):
    volume = dimensions[0] * dimensions[1] * dimensions[2]
    if volume % 7:
        return None, 0, True
    translations = product(*(range(side) for side in dimensions))
    candidates = []
    for translation in translations:
        for frame in frames:
            candidate = _candidate(frame, translation, dimensions)
            if candidate is not None:
                candidates.append(candidate)
    by_cell = [[] for _ in range(volume)]
    for index, candidate in enumerate(candidates):
        mask = candidate["mask"]
        while mask:
            bit = mask & -mask
            by_cell[bit.bit_length() - 1].append(index)
            mask -= bit

    root_index = next((i for i, item in enumerate(candidates) if item["pose"] == ROOT_POSE), None)
    if root_index is None:
        return None, 0, True
    owners = [None] * volume
    owner_cells = [None] * volume
    selected = []
    nodes = 0
    steps = tuple(
        tuple(direction if axis == selected_axis else 0 for axis in range(3))
        for selected_axis in range(3)
        for direction in (-1, 1)
    )

    def install(candidate_index):
        candidate = candidates[candidate_index]
        changed = []
        for residue, cell in candidate["canonical"].items():
            linear = _linear(residue, dimensions)
            if owners[linear] is not None:
                for old in changed:
                    owners[old] = None
                    owner_cells[old] = None
                return None
            owners[linear] = candidate_index
            owner_cells[linear] = cell
            changed.append(linear)
        for residue, cell in candidate["canonical"].items():
            for step in steps:
                neighbor_residue = _residue(
                    tuple(residue[axis] + step[axis] for axis in range(3)), dimensions
                )
                neighbor_linear = _linear(neighbor_residue, dimensions)
                neighbor_index = owners[neighbor_linear]
                if neighbor_index is None:
                    continue
                neighbor = candidates[neighbor_index]
                neighbor_cell = owner_cells[neighbor_linear]
                if not _face_compatible(candidate, cell, neighbor, neighbor_cell, step, legal):
                    for old in changed:
                        owners[old] = None
                        owner_cells[old] = None
                    return None
        return changed

    def remove(changed):
        for linear in changed:
            owners[linear] = None
            owner_cells[linear] = None

    def visit():
        nonlocal nodes
        nodes += 1
        if node_limit and nodes > node_limit:
            raise SearchLimit
        if all(owner is not None for owner in owners):
            return list(selected)
        uncovered = [index for index, owner in enumerate(owners) if owner is None]
        cell = min(
            uncovered,
            key=lambda item: sum(
                not (candidates[candidate]["mask"] & sum(1 << i for i, o in enumerate(owners) if o is not None))
                for candidate in by_cell[item]
            ),
        )
        occupied_mask = sum(1 << i for i, owner in enumerate(owners) if owner is not None)
        for candidate_index in by_cell[cell]:
            if candidates[candidate_index]["mask"] & occupied_mask:
                continue
            changed = install(candidate_index)
            if changed is None:
                continue
            selected.append(candidate_index)
            answer = visit()
            if answer is not None:
                return answer
            selected.pop()
            remove(changed)
        return None

    try:
        changed = install(root_index)
        if changed is None:
            return None, nodes, True
        selected.append(root_index)
        answer = visit()
    except SearchLimit:
        return None, nodes, False
    if answer is None:
        return None, nodes, True
    return [candidates[index]["pose"] for index in answer], nodes, True


def boxes(max_side, max_cells):
    return [
        dimensions
        for dimensions in product(range(1, max_side + 1), repeat=3)
        if dimensions[0] * dimensions[1] * dimensions[2] <= max_cells
        and dimensions[0] * dimensions[1] * dimensions[2] % 7 == 0
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-side", type=int, default=7)
    parser.add_argument("--max-cells", type=int, default=63)
    parser.add_argument(
        "--node-limit",
        type=int,
        default=0,
        help="per-box cutoff; 0 is exhaustive (cutoffs produce INCONCLUSIVE, never NONE FOUND)",
    )
    args = parser.parse_args(argv)
    certificate = load_json("certificates/candidate_certificate.json")
    frames = tuple(parse_pose([frame, [0, 0, 0]])[0] for frame in certificate["orientation_group"])
    legal = frozenset(parse_pose(item) for item in certificate["legal_contacts"])
    candidates = boxes(args.max_side, args.max_cells)
    print("R44 BOUNDED RECTANGULAR PERIOD SEARCH — EXPLORATORY ONLY")
    print(WARNING)
    print(
        f"bounds: side <= {args.max_side}, fundamental cells <= {args.max_cells}; "
        f"boxes={len(candidates)}; node_limit={args.node_limit or 'none'}"
    )
    total_nodes = 0
    complete = True
    for dimensions in candidates:
        witness, nodes, finished = search_box(dimensions, frames, legal, args.node_limit)
        total_nodes += nodes
        complete &= finished
        print(f"box={dimensions} nodes={nodes} status={'complete' if finished else 'cutoff'}")
        if witness is not None:
            print("FOUND")
            print(json.dumps({"period_box": dimensions, "poses": [pose_json(p) for p in witness]}, indent=2))
            return 0
    if complete:
        print(f"NONE FOUND (exhaustive only within the printed bounds; nodes={total_nodes})")
        return 1
    print(f"INCONCLUSIVE (one or more node cutoffs; nodes={total_nodes})")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
