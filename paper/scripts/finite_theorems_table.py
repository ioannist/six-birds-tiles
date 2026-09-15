#!/usr/bin/env python3
"""Table 1 (FIGURES.md): the finite theorems of lean/R44/R44/Theorems.lean at the pinned
commit: name, statement in words (the theorem's docstring), and decision method (from the
decision-method ledger of lean/R44/AXIOMS.md at the same commit)."""
import argparse
import re

from _texutil import common_args, finish, git_show, leanname, tex, write_rows


def main():
    ap = common_args(argparse.ArgumentParser(description=__doc__))
    args = ap.parse_args()
    src = git_show(args.commit, "lean/R44/R44/Theorems.lean")
    axioms_md = git_show(args.commit, "lean/R44/AXIOMS.md")
    methods = {}
    for m in re.finditer(r"^\| (`[^|]+`) \| ([^|]+) \|$", axioms_md, re.M):
        names = re.findall(r"`([A-Za-z0-9_]+)`", m.group(1))
        meth = m.group(2).strip().replace("`", "")
        for n in names:
            methods.setdefault(n, meth)
    items = re.findall(r"/--(.*?)-/\s*(?:set_option[^\n]*\n\s*)*theorem ([A-Za-z0-9_]+)", src, re.S)
    rows = []
    for doc, name in items:
        doc = " ".join(doc.split())
        meth = methods.get(name, "?")
        meth_tex = {"native_decide": leanname("native_decide"), "kernel decide": "kernel " + leanname("decide")}.get(meth, tex(meth))
        rows.append([leanname(name), tex(doc), meth_tex])
    names_all = re.findall(r"^theorem ([A-Za-z0-9_]+)", src, re.M)
    ok = len(rows) == len(names_all) and all(r[2] != "?" for r in rows)
    write_rows(args.out, "finite_theorems_table", rows,
               f"from lean/R44/R44/Theorems.lean docstrings and the AXIOMS.md ledger at {args.commit}",
               colspec="L{0.22\\linewidth} L{0.48\\linewidth} L{0.17\\linewidth}",
               header=["theorem", "statement (docstring)", "method"],
               longtable={"caption": "The finite theorems of the Lean development at the state described in this paper: "
                                     "statement in words (the theorem's docstring) and decision method (FIGURES.md, Table 1).",
                          "label": "tab:finite"})
    print(f"finite theorems: {len(names_all)}; rows with docstring and method: {len(rows)}")
    finish(ok, "a theorem lacks a docstring or a ledger method")


if __name__ == "__main__":
    main()
