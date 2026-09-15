#!/usr/bin/env python3
"""Generate navigation from the frozen ledger, paper annotations and supplied axiom log."""
import argparse
import hashlib
import json
import re
from pathlib import Path

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ID_RE = re.compile(r"\b([QTODARLMNHP]\d+b?|E\d)\b")
OMITTED_IDS = {"M8"}  # Prior-review status only; mathematical rows are retained verbatim.


def digest(data):
    return hashlib.sha256(data).hexdigest()


def expand_ids(text):
    ids = set(ID_RE.findall(text))
    for a, lo, b, hi in re.findall(r"\b([QTODARLMNHP])(\d+)-([QTODARLMNHP])?(\d+)\b", text):
        if not b or b == a:
            ids.update(f"{a}{i}" for i in range(int(lo), int(hi) + 1))
    return ids


def generate(root, output, pin):
    ledger_path = root / "paper/CLAIMS_LEDGER.md"
    ledger = ledger_path.read_text()
    if "[U5 SOURCE EXCERPT;" in ledger.splitlines()[0]:
        raise ValueError("map regeneration requires the original frozen ledger from the pinned repository; this package intentionally supplies a labelled excerpt without prior-review status")
    prefix, frozen = ledger.rsplit("Frozen digest (sha256", 1)
    expected = re.search(r": ([0-9a-f]{64})", frozen).group(1)
    if digest(prefix.encode()) != expected:
        raise ValueError("frozen ledger digest mismatch")
    baseline = re.search(r"Pinned to: commit ([0-9a-f]+)", ledger).group(1)
    if not pin["mathematical_baseline_commit"].startswith(baseline):
        raise ValueError("ledger mathematical baseline differs from reader pin")
    rows = {}
    for lineno, line in enumerate(ledger.splitlines(), 1):
        cells = [s.strip() for s in re.split(r"(?<!\\)\|", line)[1:-1]]
        if not cells or not re.fullmatch(r"[A-Z]\d+b?", cells[0]):
            continue
        if len(cells) == 5:
            ident, statement, tier, evidence, sections = cells
        elif len(cells) == 3:  # limitation rows have no separate evidence/tier column
            ident, statement, sections = cells
            tier, evidence = "", ""
        else:
            raise ValueError(f"unrecognized ledger row at {lineno}: {len(cells)} columns")
        if ident in OMITTED_IDS:
            continue
        rows[ident] = dict(id=ident, statement=statement, ledger_tier=tier,
                           evidence=evidence, paper_sections=sections,
                           ledger_location=f"paper/CLAIMS_LEDGER.md:{lineno}",
                           paper_locations=[], declarations=[])
    axiom_text = (root / "lean/R44/build_axioms.log").read_text()
    records = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)"
    for m in re.finditer(pattern, axiom_text, re.S):
        axioms = [s.strip() for s in (m.group(2) or "").split(",") if s.strip()]
        extra = set(axioms) - STANDARD
        tier = "T1" if not extra else "T1n" if all("._native.native_decide." in x for x in extra) else "unclassified axiom set"
        records[m.group(1)] = dict(tier=tier, axioms=axioms, supplied_record=m.group(),
            location=f"lean/R44/build_axioms.log:{axiom_text[:m.start()].count(chr(10)) + 1}")
    if "R44.r44_einstein" not in records:
        raise ValueError("missing main theorem axiom record")
    declarations = {}
    for path in sorted((root / "lean/R44/R44").rglob("*.lean")):
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            match = re.match(r"\s*(?:@\[[^]]+\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|structure|abbrev)\s+([\w.']+)", line)
            if match:
                declarations.setdefault(match.group(1), []).append(f"{path.relative_to(root)}:{lineno}")
    def names_in(text):
        text = text.replace("\\_", "_")
        tokens = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text))
        return {name for name in records if name.rsplit(".", 1)[-1] in tokens}
    for row in rows.values():
        row["declarations"] = sorted(names_in(row["statement"] + " " + row["evidence"]))
    tex_hashes = {}
    for path in sorted((root / "paper/tex").rglob("*.tex")):
        if "arxiv" in path.parts:
            continue
        tex_hashes[str(path.relative_to(root))] = digest(path.read_bytes())
        active = set()
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            match = re.search(r"%\s*ledger:\s*(.*)", line)
            if match:
                # Match the paper reconciler's annotation boundary.
                ids_text = re.split(r";\s*(?:source|sources|Lean|field|fields|figure|form|ruling|imports|generated|the|DECISIONS|Q-G)", match.group(1), 1)[0]
                active = expand_ids(ids_text)
                unknown = active - rows.keys() - OMITTED_IDS - {f"E{i}" for i in range(1, 7)} - {f"P{i}" for i in range(1, 10)}
                if unknown:
                    raise ValueError(f"unknown ledger references {path}:{lineno}: {unknown}")
                for ident in active & rows.keys():
                    rows[ident]["paper_locations"].append(f"{path.relative_to(root)}:{lineno}")
            names = set()
            for name in re.findall(r"\\lean\{([^}]+)\}", line):
                names |= names_in(name)
            for ident in active & rows.keys():
                rows[ident]["declarations"] = sorted(set(rows[ident]["declarations"]) | names)
    for name, record in records.items():
        local_name = name.removeprefix("R44.")
        locations = declarations.get(local_name, [])
        resolution = "source declaration"
        if not locations:
            locations = declarations.get(name.rsplit(".", 1)[-1], [])
            resolution = "source declaration inside namespace (name match; inspect namespace at source)"
        if not locations and name.endswith(".ext"):
            locations = declarations.get(local_name.rsplit(".", 1)[0], [])
            resolution = "Lean-generated extensionality declaration; location is the originating structure"
        record["declaration_locations"] = locations
        record["location_resolution"] = resolution if locations else "no source declaration located"
    result = dict(source_commit=pin["source_commit"], mathematical_baseline_commit=pin["mathematical_baseline_commit"],
        scope="Navigation only, not evidence. Mathematical statements and evidence are verbatim ledger cells; review-only row M8 is omitted. Paper links locate annotations. Axiom records are supplied, not freshly built.",
        omitted_ledger_rows=sorted(OMITTED_IDS),
        ledger_sha256=digest(ledger_path.read_bytes()), ledger_frozen_prefix_sha256=expected,
        axiom_log_sha256=digest(axiom_text.encode()), tex_sha256=tex_hashes,
        rows=list(rows.values()), axiom_records=records)
    output.mkdir(parents=True, exist_ok=True)
    (output / "claim_map.json").write_text(json.dumps(result, indent=2) + "\n")
    md = ["# Claim-to-evidence map — T3 navigation; T1/T1n supplied axiom records", "", result["scope"], "",
          f"Source commit: `{pin['source_commit']}`. Mathematical baseline: `{pin['mathematical_baseline_commit']}`.",
          f"Ledger SHA256: `{result['ledger_sha256']}`; frozen prefix: `{expected}`.", "",
          "Ledger D/Q/C and descriptive labels are preserved quotations, not new trust tiers. Formal tiers below are derived only from axiom sets.",
          "The main proof's sources, replay/build dependencies, and current paper checkers for O10/O11/L3/L8/L9/L10 are included. References to historical or prior-review material, optional periodicity-search evidence (N9), and illustration-production audits (O12) remain source quotations; these optional materials are excluded.",
          "Review-only ledger row M8 is omitted. The map was generated from the frozen original ledger before producing the packaged excerpt; its source digest does not describe the excerpt."]
    for row in rows.values():
        md.extend(["", f"## {row['id']} — T3 ledger quotation", "", f"Source: `{row['ledger_location']}`; paper sections: {row['paper_sections']}.", "",
            "> " + row["statement"], "", "Ledger tier (quoted): " + (row["ledger_tier"] or "not specified"),
            "", "Evidence (quoted): " + (row["evidence"] or "not separately specified"), "",
            "Paper annotation locations: " + (", ".join(f"`{x}`" for x in row["paper_locations"]) or "none directly annotated"),
            "", "Supplied axiom records: " + (", ".join(f"`{name}` ({records[name]['tier']}; `{records[name]['location']}`)" for name in row["declarations"]) or "none matched; consult the source evidence")])
    md.extend(["", "## T1/T1n — supplied axiom records, not a fresh build", ""])
    for name, record in records.items():
        md.extend([f"### {name} — {record['tier']}", "", f"Source: `{record['location']}`. Declaration locations: " + ", ".join(record["declaration_locations"]),
                   "Location interpretation: " + record["location_resolution"], "", "```text", record["supplied_record"], "```", ""])
    (output / "claim_map.md").write_text("\n".join(md) + "\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--pin", type=Path, default=Path(__file__).with_name("pin.json"))
    args = parser.parse_args()
    generate(args.root, args.out, json.loads(args.pin.read_text()))
    print("T3 STATUS: PASS (generated source navigation)")
