#!/usr/bin/env python3
"""Build exact rational members of the R44 twelve-height family.

Inputs are parsed with ``fractions.Fraction``; decimals such as ``1.25`` are
therefore checked as exact rationals, not binary floats.  With no heights the
member is c_j=j.  That default is regenerated and compared byte-for-byte with
``solid/r44_solid.json``; the first differing byte is reported on failure.
"""

from __future__ import annotations

import argparse
import csv
import json
from fractions import Fraction
from pathlib import Path

from r44 import REPOSITORY, SIMULATIONS


DEFAULT_HEIGHTS = tuple(Fraction(index) for index in range(1, 13))
ETA = Fraction(1, 100)
RHO = Fraction(1, 100)
HEIGHT_UNIT = Fraction(1, 10000)


def parse_height(text):
    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise argparse.ArgumentTypeError(f"not a rational real number: {text!r}") from error


def check_conditions(heights):
    if len(heights) != 12:
        raise ValueError(f"expected 12 component heights, received {len(heights)}")
    failures = []
    magnitudes = [abs(value) for value in heights]

    if any(value == 0 for value in heights):
        failures.append("condition 1: every c_j must be nonzero")
    repeated = sorted({value for value in magnitudes if magnitudes.count(value) > 1})
    if repeated:
        failures.append(
            "condition 1: absolute magnitudes must be distinct; repeated "
            + ", ".join(str(value) for value in repeated)
        )

    t_values = [value / 100 for value in magnitudes]
    equality = next(
        (
            (i + 1, j + 1)
            for i, left in enumerate(t_values)
            for j, right in enumerate(t_values)
            if 1 + left * left == (1 + right * right) ** 2
        ),
        None,
    )
    if equality:
        failures.append(
            "condition 2: 1+t_i^2 equals (1+t_j^2)^2 "
            f"for (i,j)={equality}"
        )

    if any(value >= 1 for value in t_values):
        failures.append("condition 3: every t_j=|c_j|/100 must be < 1")
    if any((1 + value * value) ** 2 >= 2 for value in t_values):
        failures.append("condition 3: every (1+t_j^2)^2 must be < 2")
    if 63 * max(value * value for value in t_values) >= 1:
        failures.append("condition 3: 63*max(t_j^2) must be < 1")

    if any(value * HEIGHT_UNIT >= RHO or value * HEIGHT_UNIT >= ETA for value in magnitudes):
        failures.append("condition 4: every feature height must be below rho and eta")
    return failures


def _json_number(value):
    return value.numerator if value.denominator == 1 else str(value)


def _fraction_string(value):
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def _panel_geometry():
    result = {}
    with (REPOSITORY / "solid/native_panels.csv").open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            result[int(row["panel"])] = (int(row["normal_axis"]), int(row["outward_sign"]))
    if len(result) != 24:
        raise ValueError(f"expected 24 native panels, found {len(result)}")
    return result


def build_member(heights):
    heights = tuple(heights)
    failures = check_conditions(heights)
    if failures:
        raise ValueError("; ".join(failures))
    source_path = REPOSITORY / "solid/r44_solid.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    panels = _panel_geometry()
    old_vertices = [tuple(Fraction(value) for value in vertex) for vertex in source["vertices"]]
    vertex_index = {vertex: index for index, vertex in enumerate(old_vertices)}

    new_profile = []
    for coefficient in source["profile"]:
        component = abs(int(coefficient))
        value = heights[component - 1]
        new_profile.append(value if coefficient > 0 else -value)

    for patch in source["patches"]:
        role = int(patch["role"])
        new_coefficient = new_profile[role]
        old_apex = tuple(Fraction(value) for value in patch["apex"])
        if old_apex not in vertex_index:
            raise ValueError(f"feature role {role} apex is absent from mesh vertices")
        base = [tuple(Fraction(value) for value in point) for point in patch["base"]]
        center = [sum(point[axis] for point in base) / 4 for axis in range(3)]
        normal_axis, outward_sign = panels[int(patch["face"])]
        center[normal_axis] += outward_sign * new_coefficient * HEIGHT_UNIT
        apex = tuple(center)
        source["vertices"][vertex_index[old_apex]] = [_fraction_string(value) for value in apex]
        patch["coefficient"] = _json_number(new_coefficient)
        patch["apex"] = [_fraction_string(value) for value in apex]

    source["profile"] = [_json_number(value) for value in new_profile]
    return source


def serialized_member(heights):
    return json.dumps(build_member(heights), indent=2).encode("utf-8")


def first_byte_difference(expected, actual):
    limit = min(len(expected), len(actual))
    for index in range(limit):
        if expected[index] != actual[index]:
            line = expected[:index].count(b"\n") + 1
            last_newline = expected.rfind(b"\n", 0, index)
            column = index - last_newline
            return index, line, column, expected[index], actual[index]
    if len(expected) != len(actual):
        return limit, None, None, None, None
    return None


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("heights", nargs="*", type=parse_height, help="c_1 ... c_12")
    parser.add_argument(
        "--output",
        type=Path,
        default=SIMULATIONS / "generated" / "r44_family.json",
        help="solid JSON destination",
    )
    args = parser.parse_args(argv)
    heights = tuple(args.heights) if args.heights else DEFAULT_HEIGHTS
    try:
        payload = serialized_member(heights)
    except ValueError as error:
        print(f"REJECTED: {error}")
        return 2

    source_bytes = (REPOSITORY / "solid/r44_solid.json").read_bytes()
    if heights == DEFAULT_HEIGHTS:
        difference = first_byte_difference(source_bytes, payload)
        if difference is not None:
            print(f"DEFAULT MISMATCH: first difference {difference}")
            return 1
        print("DEFAULT MATCH: regenerated member is byte-for-byte identical to solid/r44_solid.json")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(payload)
    print(f"ACCEPTED: wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

