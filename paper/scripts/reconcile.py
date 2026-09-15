#!/usr/bin/env python3
"""WRITING_PLAN.md step 15: mechanical reconciliation of paper/tex against paper/CLAIMS_LEDGER.md,
paper/refs.bib and the build's .aux. Writes paper/review/RECONCILIATION.md:
- every `% ledger:` comment's ids exist in the ledger; ledger rows never cited by any paragraph;
- every \\cite key exists in refs.bib; bib entries never cited;
- every \\cref/\\ref label is defined (from main.aux); labels never referenced;
- every paragraph's numbers (integers >= 10, with or without {,}) listed next to its ledger ids,
  so a reader can check each against its row;
- Lean names (\\lean{...}) used, against the declarations of the pinned commit.
Exit 1 if any id, key or label is missing."""
import argparse
import os
import re
import subprocess
import sys

ROOT = os.environ.get("R44_ROOT") or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
TEX = os.path.join(ROOT, "paper", "tex")
ORDER = ["main.tex", "sec1_intro.tex", "sec2_solid.tex", "sec3_finding.tex", "sec4_companions.tex",
         "sec5_registration.tex", "sec6_hierarchy.tex", "sec7_aperiodicity.tex", "sec8_mechanization.tex",
         "sec9_remarks.tex", "appA_data.tex", "appB_census.tex", "appC_lean.tex", "appD_calibration.tex",
         "notation.tex", "fig_roadmap.tex", "fig_feature_geometry.tex", "fig_companion_sectors.tex",
         "fig_collision_box.tex",
         "generated/mesh_table.tex", "generated/parameter_family_table.tex", "generated/census_table.tex",
         "generated/finite_theorems_table.tex", "generated/hypotheses_table.tex", "generated/axioms_table.tex",
         "generated/appendix_data_table.tex", "generated/atlas_44_table.tex", "generated/first_shells_table.tex",
         "generated/fig_carrier_panels.tex", "generated/fig_nesting_slice.tex", "generated/fig_coincidence.tex",
         "generated/hypotheses_record.tex"]
ID_RE = re.compile(r"\b(Q\d+|T\d+|O\d+|D\d+|A\d+|R\d+|L\d+|M\d+b?|N\d+|H\d+|P\d+|E\d)\b")
RANGE_RE = re.compile(r"\b([QTODARLMNHP])(\d+)-([QTODARLMNHP])?(\d+)\b")
# a generated/figure file stands on the ledger rows of the generator's data source
GENERATED_ROWS = {
    "generated/mesh_table.tex": "O1, O2, O3, O6, O7, O9", "generated/parameter_family_table.tex": "T14",
    "generated/census_table.tex": "R1, R2, R3, R4, R5, R6, R7, A11, L1", "generated/finite_theorems_table.tex": "M1",
    "generated/hypotheses_table.tex": "T12", "generated/axioms_table.tex": "M2", "generated/appendix_data_table.tex": "M6",
    "generated/atlas_44_table.tex": "R2, R3", "generated/first_shells_table.tex": "R4, R5, R6",
    "generated/fig_carrier_panels.tex": "O1, R1", "generated/fig_nesting_slice.tex": "O8, R8",
    "generated/fig_coincidence.tex": "L1, L8", "generated/hypotheses_record.tex": "T12",
    "fig_roadmap.tex": "roadmap: rows named in its boxes", "fig_feature_geometry.tex": "O1, O6, A5",
    "fig_companion_sectors.tex": "A2, A4, A5", "fig_collision_box.tex": "A10",
}


def expand_ids(text):
    ids = set(ID_RE.findall(text))
    for a, lo, b, hi in RANGE_RE.findall(text):
        if b and b != a:
            continue
        ids |= {f"{a}{k}" for k in range(int(lo), int(hi) + 1)}
    return ids


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--commit", default="d90313a717")
    ap.add_argument("--out", default=os.path.join(ROOT, "paper", "review", "RECONCILIATION.md"))
    args = ap.parse_args()
    ledger = open(os.path.join(ROOT, "paper", "CLAIMS_LEDGER.md"), encoding="utf-8").read()
    ledger_ids = set(re.findall(r"^\| ([A-Z]\d+b?) \|", ledger, re.M))
    errata_ids = {"E1", "E2", "E3", "E4", "E5", "E6"} | {f"P{i}" for i in range(1, 10)}  # errata; open problems P1-P9 (prose list)
    bib = open(os.path.join(ROOT, "paper", "refs.bib"), encoding="utf-8").read()
    bib_keys = set(re.findall(r"^@\w+\{([^,]+),", bib, re.M))
    aux = open(os.path.join(TEX, "main.aux"), encoding="utf-8", errors="replace").read()
    labels = {l for l in re.findall(r"\\newlabel\{([^}]+)\}", aux) if not l.endswith("@cref")}
    lean_files = [l for l in subprocess.run(["git", "-C", ROOT, "ls-tree", "-r", "--name-only", args.commit, "lean/R44"],
                                            capture_output=True, text=True).stdout.split("\n") if l.endswith(".lean")]
    lean_src = "\n".join(subprocess.run(["git", "-C", ROOT, "show", f"{args.commit}:{p}"], capture_output=True, text=True).stdout
                         for p in lean_files)
    lean_decls = set(re.findall(r"^\s*(?:private |protected |noncomputable )*(?:theorem|def|structure|lemma|abbrev|instance)\s+([A-Za-z0-9_.']+)", lean_src, re.M))
    lean_decls |= {"propext", "Classical.choice", "Quot.sound", "sorryAx", "decide", "native_decide"}
    hyp_fields = set(re.findall(r"^\| `([a-z_0-9]+)` \|", subprocess.run(["git", "-C", ROOT, "show", f"{args.commit}:lean/R44/HYPOTHESES.md"], capture_output=True, text=True).stdout, re.M))
    cited_ids, cite_keys, refs, lean_used = set(), set(), set(), set()
    report, problems, unannotated = [], [], []
    for fn in ORDER:
        path = os.path.join(TEX, fn)
        if not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8").read()
        cite_keys |= {k.strip() for m in re.finditer(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", text) for k in m.group(1).split(",")}
        refs |= {k.strip() for m in re.finditer(r"\\[cC]?ref\{([^}]+)\}", text) for k in m.group(1).split(",")}
        lean_used |= {m.group(1).replace("\\_", "_") for m in re.finditer(r"\\lean\{([^}]+)\}", text)}
        report.append(f"\n## {fn}\n")
        gen_ids = expand_ids(GENERATED_ROWS[fn]) if fn in GENERATED_ROWS else None
        if gen_ids is not None:
            cited_ids |= gen_ids
            missing = sorted(i for i in gen_ids if i not in ledger_ids and i not in errata_ids)
            report.append(f"- generated/drawn input; stands on rows: {GENERATED_ROWS[fn]}" + (f"  **MISSING {missing}**" if missing else ""))
            if missing:
                problems.append(f"{fn}: ledger ids not found {missing}")
        paras = re.split(r"\n\s*\n", text)
        active = gen_ids  # the ids of the last `% ledger:` comment cover the text up to the next comment
        for para in paras:
            m = re.search(r"%\s*ledger:\s*([^\n]*)", para)
            body = re.sub(r"%[^\n]*", "", para)
            if "\\documentclass" in body or "\\usepackage" in body:
                continue  # preamble
            structural = re.fullmatch(r"\s*(\\(begin|end)\{[a-z*]+\}[^\n]*\n?|\\(section|subsection|appendix|input|label|centering|maketitle|frontmatternote|bibliography|bibliographystyle|title|author|address|email|date|subjclass|keywords|resizebox|includegraphics|toprule|midrule|bottomrule|endhead|endfirsthead|endfoot)[^\n]*\n?|\s)*", body or " ")
            if m:
                # ids are the segment before the first "; source" / "; Lean" / "; field" clause
                id_part = re.split(r";\s*(?:source|sources|Lean|field|fields|figure|form|ruling|imports|generated|the|DECISIONS|Q-G)", m.group(1), maxsplit=1)[0]
                active = expand_ids(id_part)
                ids = active
            elif active is not None:
                if structural:
                    continue
                ids = active  # inherited coverage: reported with the same ids, its location and its numbers
            else:
                if structural or not body.strip():
                    continue
                first = re.sub(r"\s+", " ", body.strip())[:70]
                unannotated.append(f"{fn}: `{first}…`")
                continue
            cited_ids |= ids
            missing = sorted(i for i in ids if i not in ledger_ids and i not in errata_ids)
            numbers = sorted({n.replace("{,}", ",") for n in re.findall(r"(?<![\w.^/{])(\d+(?:\{,\}\d{3})*)(?![\w}])", body) if len(n.replace("{,}", "")) >= 2}, key=lambda s: int(s.replace(",", "")))
            names = sorted({t for t in re.findall(r"\\(?:thm|lem|cor|prop):?\w*", body)})
            first = re.sub(r"\s+", " ", body.strip())[:70]
            report.append(f"- `{first}…`  ids{'' if m else ' (inherited)'}: {', '.join(sorted(ids))}" + (f"  **MISSING {missing}**" if missing else "") +
                          (f"  numbers: {', '.join(numbers)}" if numbers else ""))
            if missing:
                problems.append(f"{fn}: ledger ids not found {missing}")
    report.append("\n## Cross-checks\n")
    never_cited = sorted(ledger_ids - cited_ids, key=lambda s: (s[0], int(re.sub(r"\D", "", s) or 0)))
    report.append(f"- ledger rows never cited by a paragraph comment: {', '.join(never_cited) or 'none'}")
    bad_keys = sorted(cite_keys - bib_keys)
    report.append(f"- citation keys not in refs.bib: {bad_keys or 'none'}; bib entries never cited: {sorted(bib_keys - cite_keys) or 'none'}")
    bad_refs = sorted(refs - labels)
    report.append(f"- cross-references without a label: {bad_refs or 'none'}; labels never referenced: {sorted(labels - refs) or 'none'}")
    bad_lean = sorted(n for n in lean_used if n.split(" ")[0].lstrip("\\#") not in lean_decls and n not in hyp_fields
                      and n not in {"H", "Hypotheses", "Tiling Q", "Per", "Sym", "\\#print axioms", "#print axioms", "Registration", "RegisteredPose", "CarrierHierarchy", "NativeAsymmetric Q"})
    report.append(f"- Lean names used in the text that are not declarations at {args.commit} (or record fields): {bad_lean or 'none'}")
    report.append(f"- prose paragraphs not covered by any `% ledger:` comment (a comment covers the text up to the next comment in its file; every covered paragraph is listed above with its ids and numbers): {len(unannotated)}")
    for u in unannotated:
        report.append(f"  - {u}")
    if unannotated:
        problems.append(f"{len(unannotated)} claim-bearing paragraph(s) without a ledger comment")
    problems += [f"citation keys missing: {bad_keys}"] if bad_keys else []
    problems += [f"labels missing: {bad_refs}"] if bad_refs else []
    problems += [f"Lean names unknown at pin: {bad_lean}"] if bad_lean else []
    head = ["# RECONCILIATION.md — mechanical reconciliation of the paper against its sources (step 15)\n",
            f"Generated by `paper/scripts/reconcile.py` at the pinned commit `{args.commit}`. Every paragraph with a",
            "`% ledger:` comment is listed with its ledger ids and the numbers it contains; a reader checks each number",
            "against the cited row. Cross-checks at the end.\n",
            f"**Result: {'PASS' if not problems else 'FAIL'}**" + ("" if not problems else "\n\n" + "\n".join("- " + p for p in problems))]
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    open(args.out, "w", encoding="utf-8").write("\n".join(head + report) + "\n")
    print(f"wrote {os.path.relpath(args.out, ROOT)}; problems: {len(problems)}")
    for p in problems:
        print("  " + p)
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
