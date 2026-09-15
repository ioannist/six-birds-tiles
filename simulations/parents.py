#!/usr/bin/env python3
"""Recover R44 parents from a finite registered pose list.

Only tiles whose complete 22-cell first shell is present are classified.  A
tile meeting the finite patch boundary is reported as ``undetermined`` rather
than being assigned a parent from incomplete information.  This is the finite-
patch version of the first-shell rule in PROOFS_registered.md section 7.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

from r44 import (
    REPOSITORY,
    cell_transform,
    frame_apply,
    frame_inverse,
    frame_multiply,
    load_json,
    parse_pose,
    pose_cells,
    pose_json,
    pose_multiply,
    relative_pose,
    vector_add,
    vector_scale,
)


def _candidate_parent_pose(root_pose, child_pose):
    """Parent macro pose through a root occupying the given child role."""
    child_frame, child_translation = child_pose
    inverse = frame_inverse(child_frame)
    relative_parent = (
        inverse,
        vector_scale(-1, frame_apply(inverse, child_translation)),
    )
    return pose_multiply(root_pose, relative_parent)


def _world_shell(root_pose, native_shell):
    frame, translation = root_pose
    return frozenset(
        vector_add(cell_transform(frame, cell), translation) for cell in native_shell
    )


def recover_parents(record, certificate=None):
    certificate = certificate if certificate is not None else load_json(
        "certificates/candidate_certificate.json"
    )
    pose_values = record if isinstance(record, list) else record["poses"]
    poses = tuple(parse_pose(item) for item in pose_values)
    children = tuple(parse_pose(item) for item in certificate["children"])
    legal = tuple(parse_pose(item) for item in certificate["legal_contacts"])
    legal_index = {pose: index for index, pose in enumerate(legal)}
    solution_index = {
        frozenset(indices): index for index, indices in enumerate(certificate["solutions"])
    }
    role_options = certificate["role_options"]
    native_shell = tuple(tuple(cell) for cell in certificate["shell_cells"])

    cell_sets = [pose_cells(pose) for pose in poses]
    owners = {}
    for index, cells in enumerate(cell_sets):
        for cell in cells:
            if cell in owners:
                raise ValueError(f"input has overlapping baseline cell {cell}")
            owners[cell] = index
    all_cells = frozenset(owners)

    expected_values = [] if isinstance(record, list) else record.get("construction_parents", [])
    expected_parents = {parse_pose(item) for item in expected_values}
    statuses = []
    recovered = defaultdict(list)
    errors = []
    for root_index, root_pose in enumerate(poses):
        shell = _world_shell(root_pose, native_shell)
        missing = shell - all_cells
        if missing:
            statuses.append(
                {
                    "tile": root_index,
                    "status": "undetermined",
                    "reason": "finite-patch boundary: first shell is incomplete",
                    "missing_shell_cells": len(missing),
                }
            )
            continue

        neighboring_indices = sorted({owners[cell] for cell in shell})
        atlas_indices = set()
        for neighbor_index in neighboring_indices:
            if neighbor_index == root_index:
                errors.append(f"tile {root_index}: root unexpectedly owns a shell cell")
                continue
            relative = relative_pose(root_pose, poses[neighbor_index])
            if relative not in legal_index:
                errors.append(
                    f"tile {root_index}: complete-shell neighbor {neighbor_index} is outside atlas"
                )
                continue
            atlas_indices.add(legal_index[relative])

        key = frozenset(atlas_indices)
        if key not in solution_index:
            errors.append(
                f"tile {root_index}: complete shell is not one of the certified 33 shells"
            )
            continue
        shell_id = solution_index[key]
        roles = role_options[shell_id]
        if len(roles) != 1:
            errors.append(
                f"tile {root_index}: certified shell {shell_id} has {len(roles)} parent roles"
            )
            continue
        role = roles[0]
        parent_pose = _candidate_parent_pose(root_pose, children[role])
        construction_match = None if not expected_parents else parent_pose in expected_parents
        if construction_match is False:
            errors.append(
                f"tile {root_index}: recovered parent does not match a construction parent"
            )
        recovered[parent_pose].append(root_index)
        statuses.append(
            {
                "tile": root_index,
                "status": "determined",
                "shell_id": shell_id,
                "child_role": role,
                "parent": pose_json(parent_pose),
                "construction_match": construction_match,
            }
        )

    determined = sum(status["status"] == "determined" for status in statuses)
    undetermined = sum(status["status"] == "undetermined" for status in statuses)
    return {
        "input_name": None if isinstance(record, list) else record.get("name"),
        "tile_count": len(poses),
        "determined_interior_tiles": determined,
        "undetermined_boundary_tiles": undetermined,
        "recovered_parent_count": len(recovered),
        "parent_frames": [
            {
                "pose": pose_json(parent),
                "frame": pose_json(parent)[0],
                "determined_tiles": tiles,
            }
            for parent, tiles in sorted(recovered.items())
        ],
        "construction_parent_count": len(expected_parents),
        "construction_parents_match_for_all_determined_tiles": not errors,
        "tiles": statuses,
        "errors": errors,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pose_list", type=Path, help="registered pose-list JSON from patches.py")
    parser.add_argument("--output", type=Path, help="optional machine-readable report path")
    args = parser.parse_args(argv)
    with args.pose_list.open(encoding="utf-8") as handle:
        record = json.load(handle)
    report = recover_parents(record)
    rendered = json.dumps(report, indent=2)
    print(rendered)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + "\n", encoding="utf-8")
    return 1 if report["errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
