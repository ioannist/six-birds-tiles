#!/usr/bin/env python3
"""Table 7 (FIGURES.md): the exact open conditions of the parameter family (R§11 of
proof/PROOFS_registered.md) and their values at the explicit member c_j = j, checked with
exact rationals. The conditions are transcribed from R§11; the script verifies the member."""
import argparse
from fractions import Fraction

from _texutil import common_args, finish, write_rows


def main():
    ap = common_args(argparse.ArgumentParser(description=__doc__), lean=False)
    args = ap.parse_args()
    c = [Fraction(j) for j in range(1, 13)]
    t = [abs(cj) / 100 for cj in c]
    rho = Fraction(1, 100)
    eta = Fraction(1, 100)
    height = [abs(cj) / 10000 for cj in c]
    cond1 = all(cj != 0 for cj in c) and len(set(abs(cj) for cj in c)) == 12
    cond2 = all(1 + ti * ti != (1 + tj * tj) ** 2 for ti in t for tj in t)
    tmax = max(t)
    cond3 = all(tj < 1 for tj in t) and all((1 + tj * tj) ** 2 < 2 for tj in t) and 63 * tmax * tmax < 1
    cond4 = all(h < rho and h < eta for h in height)
    gap = min(abs((1 + ti * ti) - (1 + tj * tj) ** 2) for ti in t for tj in t)
    rows = [
        ["(1) every $c_j\\ne0$, magnitudes $|c_j|$ distinct",
         "$|c_j|=1,\\dots,12$, distinct" if cond1 else "FAILS"],
        ["(2) $1+t_i^2\\ne(1+t_j^2)^2$ for all $i,j$ ($t_j=|c_j|/100$)",
         f"holds; smallest gap ${gap}$" if cond2 else "FAILS"],
        ["(3) $t_j<1$; $(1+t_j^2)^2<2$; $63\\max_j t_j^2<1$",
         f"$\\max t_j={tmax}$; $(1+t^2)^2={(1 + tmax * tmax) ** 2}$; $63t^2={63 * tmax * tmax}$" if cond3 else "FAILS"],
        ["(4) heights $|c_j|/10000$ below $\\rho=1/100$ and $\\eta=1/100$",
         f"$\\max={max(height)}$" if cond4 else "FAILS"],
    ]
    write_rows(args.out, "parameter_family_table", rows,
               "R\\S11 conditions verified at c_j = j with exact rationals",
               colspec="L{0.5\\linewidth} L{0.42\\linewidth}", header=["condition (R\\S11)", "at $c_j=j$"])
    finish(cond1 and cond2 and cond3 and cond4, "a condition fails at the explicit member")


if __name__ == "__main__":
    main()
