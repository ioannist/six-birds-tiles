#!/usr/bin/env python3
"""Table 3 (FIGURES.md): the written lemmas that formed the `Hypotheses` record, each now a
Lean theorem, at the pinned commit. Rows come from the 'Discharged' table of
lean/R44/HYPOTHESES.md (former field, theorem); the written-lemma label and the proof note come
from lean/R44/PAPER_UPDATES.md section 2; the tier is read from the theorem's own axiom line in
lean/R44/build_axioms.log (T1 = standard axioms only, T1n = named native_decide hooks). The
record itself is empty at the pin (Appendix C). Re-run with --commit at a re-pin."""
import argparse
import re

from _texutil import common_args, finish, git_show, leanname, tex, write_rows

STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def main():
    ap = common_args(argparse.ArgumentParser(description=__doc__))
    args = ap.parse_args()
    md = git_show(args.commit, "lean/R44/HYPOTHESES.md")
    sec = md.split("## Discharged", 1)[1].split("## Remaining fields", 1)[0]
    discharged = []
    for line in sec.splitlines():
        m = re.match(r"^\| `([a-z_0-9]+)` \| `R44\.([A-Za-z_0-9]+)` \| (.*) \|$", line)
        if m:
            discharged.append(m.groups())
    remaining = md.split("## Remaining fields", 1)[1]
    remaining_fields = re.findall(r"^\| `([a-z_0-9]+)` \|", remaining, re.M)

    updates = git_show(args.commit, "lean/R44/PAPER_UPDATES.md")
    notes = {}
    for line in updates.splitlines():
        m = re.match(r"^\| ([a-z_0-9]+) \(([^)]*)\) \| `R44\.([A-Za-z_0-9]+)` \| `?[0-9a-f]+`?[^|]*\| (.*) \|$", line)
        if m:
            field, label, thm, note = m.groups()
            note = note.replace("**", "")
            # Lean names inside the note become breakable \lean{} spans (no R44. prefix)
            note = re.sub(r"`(?:R44\.)?([A-Za-z_0-9]+)`", lambda m: "\x00" + m.group(1) + "\x00", note)
            notes[field] = (label, thm, note)

    log = git_show(args.commit, "lean/R44/build_axioms.log")
    axioms = {}
    for m in re.finditer(r"'R44\.([A-Za-z0-9_.']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log):
        axioms[m.group(1)] = [a.strip() for a in (m.group(2) or "").split(",") if a.strip()]

    rows = []
    problems = []
    for field, thm, delivery in discharged:
        if field not in notes:
            problems.append(f"no PAPER_UPDATES row for {field}")
            continue
        label, thm2, note = notes[field]
        if thm2 != thm:
            problems.append(f"theorem name mismatch for {field}: {thm} vs {thm2}")
        if thm not in axioms:
            problems.append(f"no axiom line for {thm}")
            continue
        hooks = [a for a in axioms[thm] if a not in STANDARD]
        if any("sorryAx" in a for a in axioms[thm]):
            problems.append(f"sorryAx in {thm}")
        tier = "T1n" if hooks else "T1"
        note_tex = "".join(leanname(part) if i % 2 else tex(part) for i, part in enumerate(note.split("\x00")))
        rows.append([leanname(field), tex(label), leanname(thm), tier, note_tex])
    write_rows(args.out, "hypotheses_table", rows,
               f"from lean/R44/HYPOTHESES.md 'Discharged', PAPER_UPDATES.md section 2 and build_axioms.log at {args.commit}; "
               f"{len(rows)} former fields; {len(remaining_fields)} remaining",
               colspec="L{0.21\\linewidth} L{0.09\\linewidth} L{0.22\\linewidth} L{0.05\\linewidth} L{0.31\\linewidth}",
               header=["former field", "written lemma", "Lean theorem", "tier", "how the formal proof argues"],
               longtable={"caption": "The written lemmas of Sections 2--5 that formed the \\lean{Hypotheses} record, each now "
                                     "a Lean theorem of the pinned development (the record is empty, Appendix C): the former "
                                     "field, the written lemma it quoted, the theorem, its tier by its own axiom line, and the "
                                     "argument of the formal proof where it differs from, or refines, the written one (FIGURES.md, Table 3).",
                          "label": "tab:hypotheses"})
    print(f"former fields: {len(rows)}; remaining fields: {len(remaining_fields)}; "
          f"tiers: T1 {sum(r[3] == 'T1' for r in rows)}, T1n {sum(r[3] == 'T1n' for r in rows)}")
    if remaining_fields:
        problems.append(f"record not empty: {remaining_fields}")
    finish(len(rows) == 19 and not problems, f"rows {len(rows)}; {problems}")


if __name__ == "__main__":
    main()
