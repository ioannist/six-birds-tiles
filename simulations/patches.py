#!/usr/bin/env python3
"""Generate and exactly check finite R44 hierarchy patches.

``sigma_depth(d)`` has 8**d physical Q-copies and 7*8**d baseline
unit cells.  The proof's nested patch ``A_n`` is the shifted even-depth patch
``sigma_depth(2*n) - c_n*(1,1,1)``, where ``c_n=2(4**n-1)/3``.

The packet's displayed counts 7, 56, 448 and 3,584 are baseline *unit cells*
at refinement depths 0 through 3.  They correspond to 1, 8, 64 and 512
copies of Q.  Section 9's A_n instead advances by two refinements at a time.
Both conventions are made explicit in every generated JSON file.
"""

from __future__ import annotations

import argparse
import json
import time
from collections import defaultdict, deque
from fractions import Fraction
from pathlib import Path

from r44 import (
    IDENTITY_FRAME,
    ROOT_POSE,
    SIMULATIONS,
    exposed_faces,
    frame_apply,
    frame_determinant,
    frame_multiply,
    load_json,
    parse_pose,
    pose_cells,
    pose_json,
    translate_pose,
    vector_add,
    vector_scale,
)


EXPECTED_CHILDREN = (
    (((0, 1, 2), (1, 1, 1)), (0, 0, 0)),
    (((1, 0, 2), (1, 1, -1)), (0, 0, 4)),
    (((0, 2, 1), (1, -1, 1)), (0, 4, 0)),
    (((2, 0, 1), (1, -1, -1)), (0, 4, 4)),
    (((2, 1, 0), (-1, 1, 1)), (4, 0, 0)),
    (((1, 2, 0), (-1, 1, -1)), (4, 0, 4)),
    (((0, 1, 2), (-1, -1, 1)), (4, 4, 0)),
    (((0, 1, 2), (1, 1, 1)), (1, 1, 1)),
)


def evidence():
    certificate = load_json("certificates/candidate_certificate.json")
    solid = load_json("solid/r44_solid.json")
    children = tuple(parse_pose(item) for item in certificate["children"])
    solid_children = tuple(parse_pose(item) for item in solid["substitution_children"])
    if children != EXPECTED_CHILDREN or solid_children != EXPECTED_CHILDREN:
        raise ValueError("the child pose table differs from PROOFS_registered.md section 1")
    if any(frame_determinant(frame) != 1 for frame, _ in children):
        raise ValueError("a substitution child frame is not a proper rotation")
    legal = frozenset(parse_pose(item) for item in certificate["legal_contacts"])
    if len(legal) != 44:
        raise ValueError(f"expected the 44-contact atlas, found {len(legal)}")
    return children, legal, solid


def refine_pose(pose, children=EXPECTED_CHILDREN):
    """Apply the exact refinement formula (G,t)->(GH,2t+Gu)."""
    frame, translation = pose
    return tuple(
        (
            frame_multiply(frame, child_frame),
            vector_add(vector_scale(2, translation), frame_apply(frame, child_translation)),
        )
        for child_frame, child_translation in children
    )


def sigma_depth(depth, children=EXPECTED_CHILDREN):
    if depth < 0:
        raise ValueError("refinement depth must be nonnegative")
    poses = (ROOT_POSE,)
    for _ in range(depth):
        poses = tuple(child for pose in poses for child in refine_pose(pose, children))
    return poses


def proof_shift(level):
    if level < 0:
        raise ValueError("nested level must be nonnegative")
    return 2 * (4**level - 1) // 3


def nested_patch(level, children=EXPECTED_CHILDREN):
    shift = proof_shift(level)
    return tuple(
        translate_pose(pose, (-shift, -shift, -shift))
        for pose in sigma_depth(2 * level, children)
    )


def check_two_refinement_embedding(depth, shallow=None, deep=None):
    """Check the same-frame grandchild copy sigma^d(P)+2^(d+1) in sigma^(d+2)(P)."""
    shallow = tuple(shallow if shallow is not None else sigma_depth(depth))
    deep = frozenset(deep if deep is not None else sigma_depth(depth + 2))
    offset = (2 ** (depth + 1),) * 3
    expected = {translate_pose(pose, offset) for pose in shallow}
    missing = expected - deep
    if missing:
        raise AssertionError(f"two-refinement grandchild embedding misses {len(missing)} poses")
    return {"depth": depth, "offset": list(offset), "embedded_pose_count": len(expected)}


def check_nested_pair(level, shallow=None, deep=None):
    shallow = frozenset(shallow if shallow is not None else nested_patch(level))
    deep = frozenset(deep if deep is not None else nested_patch(level + 1))
    missing = shallow - deep
    if missing:
        raise AssertionError(f"A_{level} is not a literal subpatch of A_{level + 1}")
    return {
        "from_level": level,
        "to_level": level + 1,
        "c_from": proof_shift(level),
        "c_to": proof_shift(level + 1),
        "embedded_pose_count": len(shallow),
    }


def check_patch(poses, legal_contacts):
    """Check disjoint cells and every baseline face contact against the atlas."""
    owners = {}
    cell_sets = []
    for index, pose in enumerate(poses):
        cells = pose_cells(pose)
        if len(cells) != 7:
            raise AssertionError(f"pose {index} does not have seven baseline cells")
        for cell in cells:
            if cell in owners:
                raise AssertionError(
                    f"baseline cell {cell} is shared by poses {owners[cell]} and {index}"
                )
            owners[cell] = index
        cell_sets.append(cells)

    face_owners = defaultdict(list)
    for index, pose in enumerate(poses):
        for key, side in exposed_faces(pose).items():
            face_owners[key].append((index, side))

    adjacent_pairs = set()
    contact_face_count = 0
    from r44 import relative_pose  # keep the public checker imports compact

    for key, records in face_owners.items():
        if len(records) > 2:
            raise AssertionError(f"more than two tiles meet baseline face {key}")
        if len(records) != 2:
            continue
        (left, left_side), (right, right_side) = records
        if left_side != -right_side:
            raise AssertionError(f"inconsistent orientations at baseline face {key}")
        adjacent_pairs.add((min(left, right), max(left, right)))
        contact_face_count += 1

    for left, right in adjacent_pairs:
        relative = relative_pose(poses[left], poses[right])
        if relative not in legal_contacts:
            reverse = relative_pose(poses[right], poses[left])
            raise AssertionError(
                "face-adjacent pair is outside the 44 atlas: "
                f"poses {left},{right}; relative={relative}; reverse={reverse}"
            )

    components = 0
    if poses:
        graph = defaultdict(set)
        for left, right in adjacent_pairs:
            graph[left].add(right)
            graph[right].add(left)
        seen = set()
        for start in range(len(poses)):
            if start in seen:
                continue
            components += 1
            queue = deque([start])
            seen.add(start)
            while queue:
                for neighbor in graph[queue.popleft()]:
                    if neighbor not in seen:
                        seen.add(neighbor)
                        queue.append(neighbor)

    return {
        "tile_count": len(poses),
        "baseline_cell_count": len(owners),
        "cells_disjoint": True,
        "face_adjacent_tile_pairs": len(adjacent_pairs),
        "shared_baseline_faces": contact_face_count,
        "all_face_contacts_in_44_atlas": True,
        "contact_graph_components": components,
    }


def construction_parent_poses(previous_level):
    """Parent macro poses in the fine coordinate scale of their children."""
    return tuple((frame, vector_scale(2, translation)) for frame, translation in previous_level)


def patch_record(depth, poses, checks, previous_level=None):
    record = {
        "schema": "r44-registered-pose-list-v1",
        "name": f"sigma_{depth}",
        "refinement_depth": depth,
        "tile_count": len(poses),
        "baseline_cell_count": 7 * len(poses),
        "poses": [pose_json(pose) for pose in poses],
        "checks": checks,
        "section_9_note": (
            "The proof's nested A_n is sigma_(2n) shifted by "
            "-c_n(1,1,1), c_n=2(4^n-1)/3."
        ),
    }
    if depth % 2 == 0:
        level = depth // 2
        record["proof_A_level"] = level
        record["proof_shift_c_n"] = proof_shift(level)
    if previous_level is not None:
        record["construction_parents"] = [
            pose_json(pose) for pose in construction_parent_poses(previous_level)
        ]
    return record


def _fraction_vector(values):
    return tuple(Fraction(value) for value in values)


def _triangle_materials(solid):
    vertices = [tuple(Fraction(value) for value in vertex) for vertex in solid["vertices"]]
    vertex_index = {vertex: index for index, vertex in enumerate(vertices)}
    apex_material = {}
    for patch in solid["patches"]:
        apex = _fraction_vector(patch["apex"])
        apex_material[vertex_index[apex]] = "positive" if patch["coefficient"] > 0 else "negative"
    materials = []
    for triangle in solid["triangles"]:
        kinds = {apex_material[index] for index in triangle if index in apex_material}
        materials.append(next(iter(kinds)) if kinds else "baseline")
    return vertices, materials


def _decimal(value):
    return format(float(value), ".12g")


def export_obj(poses, destination, solid=None):
    """Stream physical Q copies to an OBJ and a three-material MTL file."""
    destination = Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    solid = solid if solid is not None else load_json("solid/r44_solid.json")
    vertices, materials = _triangle_materials(solid)
    triangles_by_material = {
        name: [triangle for triangle, material in zip(solid["triangles"], materials) if material == name]
        for name in ("baseline", "positive", "negative")
    }
    mtl_path = destination.with_suffix(".mtl")
    mtl_path.write_text(
        "newmtl baseline\nKd 0.72 0.76 0.82\n\n"
        "newmtl positive\nKd 0.88 0.22 0.18\n\n"
        "newmtl negative\nKd 0.16 0.36 0.86\n",
        encoding="utf-8",
    )
    with destination.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write("# R44 physical patch; visualization only, not theorem evidence.\n")
        handle.write(f"mtllib {mtl_path.name}\n")
        for frame, translation in poses:
            for vertex in vertices:
                point = vector_add(frame_apply(frame, vertex), translation)
                handle.write("v " + " ".join(_decimal(value) for value in point) + "\n")
        vertex_count = len(vertices)
        for pose_index, (frame, _) in enumerate(poses):
            offset = pose_index * vertex_count + 1
            reverse = frame_determinant(frame) < 0
            handle.write(f"g tile_{pose_index}\n")
            for material in ("baseline", "positive", "negative"):
                handle.write(f"usemtl {material}\n")
                for triangle in triangles_by_material[material]:
                    indices = list(reversed(triangle)) if reverse else triangle
                    handle.write("f " + " ".join(str(offset + index) for index in indices) + "\n")
    return {
        "obj": str(destination),
        "mtl": str(mtl_path),
        "vertices": len(poses) * len(vertices),
        "triangles": len(poses) * len(solid["triangles"]),
    }


def write_refinement_patches(max_depth, output_dir, obj_through=2):
    children, legal, solid = evidence()
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    levels = []
    results = []
    poses = (ROOT_POSE,)
    for depth in range(max_depth + 1):
        levels.append(poses)
        checks = check_patch(poses, legal)
        record = patch_record(depth, poses, checks, levels[depth - 1] if depth else None)
        json_path = output_dir / f"sigma_{depth}.json"
        json_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        result = {"depth": depth, "json": str(json_path), **checks}
        if depth <= obj_through:
            result["obj"] = export_obj(poses, output_dir / f"sigma_{depth}.obj", solid)
        results.append(result)
        if depth < max_depth:
            poses = tuple(child for pose in poses for child in refine_pose(pose, children))

    embeddings = []
    for depth in range(max(0, max_depth - 1)):
        if depth + 2 <= max_depth:
            embeddings.append(check_two_refinement_embedding(depth, levels[depth], levels[depth + 2]))
    nested = []
    for level in range(max_depth // 2):
        shallow_shift = proof_shift(level)
        deep_shift = proof_shift(level + 1)
        shallow = tuple(translate_pose(p, (-shallow_shift,) * 3) for p in levels[2 * level])
        deep = tuple(translate_pose(p, (-deep_shift,) * 3) for p in levels[2 * level + 2])
        nested.append(check_nested_pair(level, shallow, deep))
    return {"patches": results, "two_refinement_embeddings": embeddings, "nested_A_pairs": nested}


def write_proof_patches(max_level, output_dir, obj_through=-1):
    """Write the literal section-9 A_n sequence (which uses depth 2*n)."""
    children, legal, solid = evidence()
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    results = []
    previous = None
    for level in range(max_level + 1):
        poses = nested_patch(level, children)
        checks = check_patch(poses, legal)
        if previous is not None:
            nesting = check_nested_pair(level - 1, previous, poses)
        else:
            nesting = None
        record = {
            "schema": "r44-registered-pose-list-v1",
            "name": f"A_{level}",
            "proof_section": "PROOFS_registered.md section 9",
            "proof_A_level": level,
            "refinement_depth": 2 * level,
            "proof_shift_c_n": proof_shift(level),
            "tile_count": len(poses),
            "baseline_cell_count": 7 * len(poses),
            "poses": [pose_json(pose) for pose in poses],
            "checks": checks,
            "nested_from_previous": nesting,
        }
        if level > 0:
            immediate_previous = sigma_depth(2 * level - 1, children)
            offset = (-proof_shift(level),) * 3
            record["construction_parents"] = [
                pose_json(translate_pose(parent, offset))
                for parent in construction_parent_poses(immediate_previous)
            ]
        json_path = output_dir / f"A_{level}.json"
        json_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        result = {"level": level, "json": str(json_path), **checks}
        if level <= obj_through:
            result["obj"] = export_obj(poses, output_dir / f"A_{level}.obj", solid)
        results.append(result)
        previous = poses
    return results


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-depth", type=int, default=3, choices=range(0, 8))
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=SIMULATIONS / "generated",
        help="directory for pose JSON, OBJ and MTL outputs",
    )
    parser.add_argument(
        "--obj-through",
        type=int,
        default=2,
        help="export physical Q-copy OBJ files through this refinement depth (-1 disables)",
    )
    parser.add_argument(
        "--proof-max-level",
        type=int,
        choices=range(0, 4),
        help=(
            "also write the literal nested A_0...A_N sequence; A_N has 64**N tiles, "
            "so level 3 is intentionally large"
        ),
    )
    parser.add_argument(
        "--proof-obj-through",
        type=int,
        default=-1,
        help="OBJ limit for literal proof A_n patches (disabled by default)",
    )
    args = parser.parse_args(argv)
    started = time.monotonic()
    report = write_refinement_patches(args.max_depth, args.output_dir, args.obj_through)
    if args.proof_max_level is not None:
        report["proof_A_patches"] = write_proof_patches(
            args.proof_max_level,
            args.output_dir,
            args.proof_obj_through,
        )
    report["seconds"] = time.monotonic() - started
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
