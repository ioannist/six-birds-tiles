#!/usr/bin/env python3
"""Exact finite controls for the native normal-tube formulas.

These 4,800 rational samples, promoted from the external round-2 review's
``analytic_scope_controls.py``, exercise both inverse identities, the
hypograph transport, and agreement after reversing the two incident owners'
normal coordinates. They are finite controls, not a proof of the continuous
homeomorphism or of tube gluing.
"""

from fractions import Fraction as F


RHO = F(1, 100)
ETA = RHO
HEIGHTS = [F(j, 10_000) for j in range(-12, 13) if j]
TANGENT_GRID = [-ETA, -ETA / 2, F(0), ETA / 2, ETA]
NORMAL_GRID = [-2 * RHO, -RHO, -RHO / 2, F(0), RHO / 2, RHO, 2 * RHO]


def tent_height(height: F, u: F, v: F) -> F:
    return height * max(F(0), 1 - max(abs(u), abs(v)) / ETA)


def forward(z: F, b: F) -> F:
    return z + max(F(0), 1 - abs(z) / RHO) * b


def inverse(y: F, b: F) -> F:
    if abs(y) >= RHO:
        return y
    if y <= b:
        return (y - b) / (1 + b / RHO)
    return (y - b) / (1 - b / RHO)


def main() -> int:
    cases = 0
    for height in HEIGHTS:
        for u in TANGENT_GRID:
            for v in TANGENT_GRID:
                b = tent_height(height, u, v)
                assert abs(b) < RHO
                for z in NORMAL_GRID + [b]:
                    assert inverse(forward(z, b), b) == z
                    assert forward(inverse(z, b), b) == z
                    assert (z <= 0) == (forward(z, b) <= b)
                    other_owner = -forward(-z, -b)
                    assert forward(z, b) == other_owner
                    cases += 1
    assert cases == 4_800
    print(
        "tube_formula_controls: PASS "
        "(cases=4800, inverse-after-forward=4800, "
        "forward-after-inverse=4800, hypograph=4800, two-owner=4800)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
