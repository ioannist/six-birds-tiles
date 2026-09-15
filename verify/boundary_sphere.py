#!/usr/bin/env python3
"""Independently verify that the R44 boundary mesh is a combinatorial sphere.

Standard library only.  The four checks use the indexed triangles in the
canonical solid JSON and exact integer combinatorics; coordinate values and
the summary counts stored in the JSON are not trusted.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CANONICAL_SOLID = ROOT / "solid/r44_solid.json"


class CheckFailure(Exception):
    """A boundary-sphere obligation failed."""


def edge(a: int, b: int) -> tuple[int, int]:
    return (a, b) if a < b else (b, a)


def connected(start: int, neighbors: dict[int, set[int]]) -> set[int]:
    seen = {start}
    pending = [start]
    while pending:
        current = pending.pop()
        for other in neighbors[current] - seen:
            seen.add(other)
            pending.append(other)
    return seen


def verify(path: Path) -> tuple[int, int, int, int]:
    data = json.loads(path.read_text())
    vertices = data["vertices"]
    triangles = data["triangles"]
    vertex_count = len(vertices)
    triangle_count = len(triangles)

    edge_faces: dict[tuple[int, int], list[int]] = defaultdict(list)
    vertex_link_edges: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for face, triangle in enumerate(triangles):
        if not (isinstance(triangle, list) and len(triangle) == 3):
            raise CheckFailure(f"triangle {face} is not an indexed triple")
        a, b, c = triangle
        if not all(isinstance(v, int) and 0 <= v < vertex_count for v in triangle):
            raise CheckFailure(f"triangle {face} has an invalid vertex index: {triangle!r}")
        if len({a, b, c}) != 3:
            raise CheckFailure(f"triangle {face} is degenerate: {triangle!r}")
        for side in (edge(a, b), edge(b, c), edge(c, a)):
            edge_faces[side].append(face)
        vertex_link_edges[a].append(edge(b, c))
        vertex_link_edges[b].append(edge(c, a))
        vertex_link_edges[c].append(edge(a, b))

    bad_edges = [(side, faces) for side, faces in edge_faces.items() if len(faces) != 2]
    if bad_edges:
        side, faces = bad_edges[0]
        raise CheckFailure(
            f"edge incidence: {len(bad_edges)} edges do not have two incident triangles; "
            f"first is {side} with triangles {faces}"
        )

    face_neighbors = [set() for _ in triangles]
    for first, second in edge_faces.values():
        face_neighbors[first].add(second)
        face_neighbors[second].add(first)
    if not triangles:
        raise CheckFailure("triangle adjacency: the mesh has no triangles")
    reached_faces = connected(0, dict(enumerate(face_neighbors)))
    if len(reached_faces) != triangle_count:
        raise CheckFailure(
            f"triangle adjacency: reached {len(reached_faces)} of {triangle_count} triangles"
        )

    for vertex in range(vertex_count):
        link_edges = vertex_link_edges[vertex]
        if not link_edges:
            raise CheckFailure(f"vertex link {vertex}: no incident triangles")
        duplicate_edges = [side for side, count in Counter(link_edges).items() if count != 1]
        if duplicate_edges:
            raise CheckFailure(
                f"vertex link {vertex}: repeated link edge {duplicate_edges[0]}"
            )
        link_neighbors: dict[int, set[int]] = defaultdict(set)
        link_degree: Counter[int] = Counter()
        for a, b in link_edges:
            link_neighbors[a].add(b)
            link_neighbors[b].add(a)
            link_degree[a] += 1
            link_degree[b] += 1
        bad_degree = [(v, degree) for v, degree in link_degree.items() if degree != 2]
        if bad_degree:
            raise CheckFailure(
                f"vertex link {vertex}: link vertex {bad_degree[0][0]} "
                f"has degree {bad_degree[0][1]}, not two"
            )
        start = next(iter(link_neighbors))
        reached_link = connected(start, link_neighbors)
        if len(reached_link) != len(link_neighbors):
            raise CheckFailure(
                f"vertex link {vertex}: reached {len(reached_link)} of "
                f"{len(link_neighbors)} link vertices"
            )

    edge_count = len(edge_faces)
    euler_characteristic = vertex_count - edge_count + triangle_count
    if (vertex_count, edge_count, triangle_count, euler_characteristic) != (2138, 6408, 4272, 2):
        raise CheckFailure(
            "Euler characteristic: computed "
            f"V={vertex_count}, E={edge_count}, F={triangle_count}, "
            f"V-E+F={euler_characteristic}"
        )
    return vertex_count, edge_count, triangle_count, euler_characteristic


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("solid", nargs="?", type=Path, default=CANONICAL_SOLID)
    args = parser.parse_args()
    try:
        vertex_count, edge_count, triangle_count, chi = verify(args.solid)
    except (CheckFailure, KeyError, json.JSONDecodeError, OSError) as error:
        print(f"boundary_sphere: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "boundary_sphere: PASS "
        f"(edges=two, triangle_graph=connected, vertex_links=cycles, "
        f"V={vertex_count}, E={edge_count}, F={triangle_count}, chi={chi})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
