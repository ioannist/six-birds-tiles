#!/usr/bin/env python3
"""Close the R44 legal 2x2x2 block language and classify fixed seeds.

The substitution is reconstructed from the canonical certificate using only
the tuple geometry shared by ``substitution_modular_coincidence``.  No block
table, seed list, or bounded patch search is used: the first-level blocks are
closed under every 2x2x2 window of their substituted 4x4x4 blocks until no new
block is produced.

An optional certificate path is accepted for mutation controls.  Standard
library only; do not run with ``python -O``.
"""

import itertools
import json
import sys
from collections import Counter
from pathlib import Path

import substitution_modular_coincidence as substitution


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CERTIFICATE = ROOT / "certificates/candidate_certificate.json"
BITS = tuple(itertools.product((0, 1), repeat=3))
SEED_POSITIONS = tuple(itertools.product((-1, 0), repeat=3))
WINDOW_ORIGINS = tuple(itertools.product(range(3), repeat=3))
EXPECTED_CLOSURE_SIZES = [168, 600, 1278, 1398, 1410, 1410]


class CheckFailure(RuntimeError):
    """A certificate or expected-result check failed."""


def require(condition, message):
    if not condition:
        raise CheckFailure(message)


def certificate_path(argv):
    require(len(argv) <= 2, f"usage: {argv[0]} [certificate.json]")
    return Path(argv[1]).resolve() if len(argv) == 2 else DEFAULT_CERTIFICATE


def reconstruct_phi(path):
    raw = json.loads(path.read_text())
    frames = tuple(substitution.frame_from_json(item)
                   for item in raw["orientation_group"])
    children = tuple(
        (substitution.frame_from_json(item[0]), tuple(item[1]))
        for item in raw["children"]
    )
    require(len(frames) == len(set(frames)) == 24,
            f"expected 24 distinct proper frames, got {len(frames)}")
    require(len(children) == 8,
            f"expected 8 child poses, got {len(children)}")

    labels = tuple((frame, cell) for frame in frames
                   for cell in substitution.CHAIR_CELLS)
    label_index = {label: i for i, label in enumerate(labels)}
    require(len(labels) == len(label_index) == 168,
            f"expected 168 distinct labels, got {len(label_index)}")

    phi = {}
    for frame in frames:
        owners = {}
        for child_frame, child_origin in substitution.child_poses(frame, children):
            require(child_frame in frames,
                    "transformed child frame is outside the orientation group")
            for child_cell in substitution.CHAIR_CELLS:
                point = substitution.cell_lower(
                    child_frame, child_origin, child_cell)
                owners.setdefault(point, []).append((child_frame, child_cell))

        doubled = {
            substitution.add(
                substitution.scale(
                    2, substitution.cell_lower(frame, substitution.ORIGIN, cell)),
                digit,
            )
            for cell in substitution.CHAIR_CELLS
            for digit in BITS
        }
        require(set(owners) == doubled,
                "child cells do not cover the doubled chair")
        require(all(len(found) == 1 for found in owners.values()),
                "child cells do not cover the doubled chair uniquely")

        for cell in substitution.CHAIR_CELLS:
            source = substitution.cell_lower(frame, substitution.ORIGIN, cell)
            source_index = label_index[(frame, cell)]
            for digit in BITS:
                target_point = substitution.add(
                    substitution.scale(2, source), digit)
                target_label, = owners[target_point]
                phi[source_index, digit] = label_index[target_label]

    require(len(phi) == 168 * 8,
            f"expected 1344 substitution entries, got {len(phi)}")
    return frames, children, labels, label_index, phi


def substituted_window(block, origin, phi):
    values = []
    for offset in BITS:
        point = tuple(origin[i] + offset[i] for i in range(3))
        parent = tuple(coordinate // 2 for coordinate in point)
        residue = tuple(coordinate % 2 for coordinate in point)
        values.append(phi[block[BITS.index(parent)], residue])
    return tuple(values)


def close_block_language(phi):
    language = {tuple(phi[label, digit] for digit in BITS)
                for label in range(168)}
    frontier = set(language)
    sizes = [len(language)]
    while frontier:
        discovered = {
            substituted_window(block, origin, phi)
            for block in frontier
            for origin in WINDOW_ORIGINS
        } - language
        language.update(discovered)
        frontier = discovered
        sizes.append(len(language))
    stable = not {
        substituted_window(block, origin, phi)
        for block in language
        for origin in WINDOW_ORIGINS
    } - language
    return language, sizes, stable


def fixed_seeds(language, phi):
    residues = tuple(tuple(coordinate % 2 for coordinate in point)
                     for point in SEED_POSITIONS)
    return tuple(sorted(
        block for block in language
        if all(phi[block[i], residues[i]] == block[i] for i in range(8))
    ))


def substitute_configuration(configuration, phi):
    return {
        substitution.add(substitution.scale(2, point), digit): phi[label, digit]
        for point, label in configuration.items()
        for digit in BITS
    }


def act_configuration(frame, configuration, labels, label_index):
    return {
        substitution.cell_lower(frame, substitution.ORIGIN, point):
            label_index[(substitution.compose(frame, labels[label][0]),
                         labels[label][1])]
        for point, label in configuration.items()
    }


def act_seed(frame, seed, labels, label_index):
    moved = act_configuration(
        frame, dict(zip(SEED_POSITIONS, seed)), labels, label_index)
    require(set(moved) == set(SEED_POSITIONS),
            "proper frame did not preserve the seed cube")
    return tuple(moved[position] for position in SEED_POSITIONS)


def classify_seeds(seeds, frames, labels, label_index):
    seed_set = set(seeds)
    remaining = set(seeds)
    orbits = []
    stabilizer_orders = []
    while remaining:
        seed = min(remaining)
        orbit = {act_seed(frame, seed, labels, label_index)
                 for frame in frames}
        require(orbit <= seed_set, "proper frame takes a fixed seed outside the language")
        orbits.append(orbit)
        remaining -= orbit
    for seed in seeds:
        stabilizer_orders.append(sum(
            act_seed(frame, seed, labels, label_index) == seed
            for frame in frames
        ))
    return sorted(len(orbit) for orbit in orbits), Counter(stabilizer_orders)


def check_in_place_reproduction(seeds, phi):
    for seed in seeds:
        configuration = dict(zip(SEED_POSITIONS, seed))
        refined = substitute_configuration(configuration, phi)
        require(all(refined[position] == label
                    for position, label in configuration.items()),
                "a fixed seed did not reproduce itself in place")


def check_frame_commutation(frames, children, labels, label_index, phi):
    configuration_checks = 0
    test_points = ((0, 0, 0), (-1, 0, 0), (2, -3, 1))
    for frame in frames:
        for label in range(168):
            for point in test_points:
                configuration = {point: label}
                left = substitute_configuration(
                    act_configuration(frame, configuration, labels, label_index), phi)
                right = act_configuration(
                    frame, substitute_configuration(configuration, phi),
                    labels, label_index)
                require(left == right,
                        "substitution does not commute with a frame on labelled cells")
                configuration_checks += 1

    pose_checks = 0
    for outer in frames:
        for parent in frames:
            left = sorted(substitution.child_poses(
                substitution.compose(outer, parent), children))
            right = sorted(
                (substitution.compose(outer, child_frame),
                 substitution.act(outer, child_origin))
                for child_frame, child_origin
                in substitution.child_poses(parent, children)
            )
            require(left == right,
                    "substitution does not commute with a frame on child poses")
            pose_checks += 1
    return configuration_checks, pose_checks


def main(argv=None):
    argv = sys.argv if argv is None else argv
    try:
        require(sys.flags.optimize == 0,
                "run without -O (assertions must be enabled)")
        path = certificate_path(argv)
        frames, children, labels, label_index, phi = reconstruct_phi(path)
        language, sizes, stable = close_block_language(phi)
        seeds = fixed_seeds(language, phi)
        orbit_sizes, stabilizer_histogram = classify_seeds(
            seeds, frames, labels, label_index)
        check_in_place_reproduction(seeds, phi)
        configuration_checks, pose_checks = check_frame_commutation(
            frames, children, labels, label_index, phi)

        print(f"language closure sizes: {sizes[:-1]}; stable: {stable}")
        print(f"fixed seeds: {len(seeds)}")
        print(f"seed orbit sizes: {orbit_sizes}")
        print("origin stabilizer histogram: "
              f"{dict(sorted(stabilizer_histogram.items()))}")
        print(f"in-place seed reproduction: PASS ({len(seeds)}/{len(seeds)})")
        print("frame commutation: PASS "
              f"({configuration_checks} labelled-cell, {pose_checks} child-pose checks)")

        require(sizes == EXPECTED_CLOSURE_SIZES,
                f"closure sizes differ from {EXPECTED_CLOSURE_SIZES}")
        require(stable, "final block language is not stable")
        require(len(seeds) == 27, "fixed-seed count differs from 27")
        require(orbit_sizes == [3, 24], "seed orbit sizes differ from [3, 24]")
        require(stabilizer_histogram == Counter({1: 24, 8: 3}),
                "origin stabilizer histogram differs from {1: 24, 8: 3}")
        print("STATUS: PASS")
        return 0
    except (CheckFailure, KeyError, ValueError, json.JSONDecodeError) as error:
        print(f"STATUS: FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
