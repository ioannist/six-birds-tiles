#!/usr/bin/env python3
"""Table 4 (FIGURES.md): axiom lines of the finite theorems and of the spine theorems, read
from lean/R44/build_axioms.log at the pinned commit (re-run with --commit at freeze).
Each row compresses the `#print axioms` set: 'none', 'standard' (propext, Classical.choice,
Quot.sound), and the named `native_decide` hooks."""
import argparse
import re

from _texutil import common_args, finish, git_show, leanname, tex, write_rows

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
SPINE = ["r44_einstein", "tiling_homochiral", "tiling_chirality_corollary", "carrier_hierarchy",
         "carrier_hierarchy_unique", "substitution_modular_coincidence"]


def parse_log(text):
    sets = {}
    for m in re.finditer(r"'R44\.([A-Za-z0-9_.']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text):
        name, body = m.group(1), m.group(2)
        axioms = [a.strip() for a in body.split(",")] if body else []
        sets[name] = axioms
    return sets


def compress(axioms):
    std = sorted(a for a in axioms if a in STANDARD)
    hooks = sorted(a for a in axioms if "_native.native_decide" in a)
    other = sorted(a for a in axioms if a not in STANDARD and "_native.native_decide" not in a)
    parts = []
    if not axioms:
        return "none"
    if std:
        parts.append("standard" if len(std) == 3 else ", ".join(tex(a) for a in std))
    if hooks:
        names = [h.split("._native")[0].replace("R44.", "") for h in hooks]
        parts.append(f"hooks: {', '.join(tex(n) for n in names)}" if len(names) <= 3
                     else f"{len(names)} hooks ({', '.join(tex(n) for n in names[:2])}, \\dots)")
    if other:
        parts.append(", ".join(tex(a) for a in other))
    return "; ".join(parts)


def main():
    ap = common_args(argparse.ArgumentParser(description=__doc__))
    args = ap.parse_args()
    log = git_show(args.commit, "lean/R44/build_axioms.log")
    theorems_src = git_show(args.commit, "lean/R44/R44/Theorems.lean")
    finite = re.findall(r"^theorem ([A-Za-z0-9_]+)", theorems_src, re.M)
    sets = parse_log(log)
    missing = [n for n in finite + SPINE if n not in sets]
    rows = []
    for n in finite + SPINE:
        if n in sets:
            rows.append([leanname(n), compress(sets[n])])
    sorry = [n for n, ax in sets.items() if any("sorryAx" in a for a in ax)]
    core_sorry = [n for n in finite + SPINE if n in sets and any("sorryAx" in a for a in sets[n])]
    write_rows(args.out, "axioms_table", rows,
               f"from lean/R44/build_axioms.log at {args.commit}; {len(sets)} declarations with an axiom line",
               colspec="L{0.3\\linewidth} L{0.58\\linewidth}", header=["declaration", "axioms (\\texttt{\\#print axioms})"],
               longtable={"caption": "Axiom lines: the output of \\lean{\\#print axioms} for the finite theorems and the main "
                                     "theorems; ``standard'' is \\lean{propext}, \\lean{Classical.choice}, \\lean{Quot.sound}, and "
                                     "hooks are the per-theorem \\lean{native\\_decide} axioms (FIGURES.md, Table 4).",
                          "label": "tab:axioms"})
    print(f"declarations in log: {len(sets)}; finite theorems: {len(finite)}; sorryAx anywhere: {len(sorry)} "
          f"({', '.join(sorry) if sorry else 'none'}); sorryAx in core rows: {len(core_sorry)}")
    finish(not missing and not core_sorry, f"missing {missing} or sorryAx in core {core_sorry}")


if __name__ == "__main__":
    main()
