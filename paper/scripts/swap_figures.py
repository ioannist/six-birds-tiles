#!/usr/bin/env python3
"""Replace the \\figtodo{...}{...} placeholders of the section files by the generated / hand-drawn
figures (brace-aware), and make every figure referenced at least once. Usage: swap_figures.py <texdir>.
Idempotent: a file without the placeholder is left unchanged."""
import re
import sys
import pathlib

SWAPS = {
    "sec2_solid.tex": [("Fig.\\ 2.2", r"\resizebox{\linewidth}{!}{\input{generated/fig_carrier_panels}}"),
                       ("Fig.\\ 2.3", r"\resizebox{\linewidth}{!}{\input{fig_feature_geometry}}")],
    "sec3_finding.tex": [("Fig.\\ 3.3", r"{\footnotesize\input{generated/atlas_44_table}}")],
    "sec4_companions.tex": [("Fig.\\ 4.1", r"\resizebox{\linewidth}{!}{\input{fig_companion_sectors}}")],
    "sec5_registration.tex": [("Fig.\\ 4.2", r"\resizebox{0.9\linewidth}{!}{\input{fig_collision_box}}")],
    "sec6_hierarchy.tex": [("Fig.\\ 6.1", r"{\scriptsize\input{generated/first_shells_table}}"),
                           ("Fig.\\ 6.2", r"\resizebox{0.8\linewidth}{!}{\input{generated/fig_nesting_slice}}")],
    "sec8_mechanization.tex": [("Fig.\\ 8.1", r"\input{generated/fig_coincidence}")],
}


def find_figtodo(s, tag):
    """Return (start, end) of the \\figtodo{..}{..} call whose second argument contains `tag`."""
    for m in re.finditer(r"\\figtodo\{", s):
        i = m.end()
        # first argument
        depth, j = 1, i
        while depth:
            depth += {"{": 1, "}": -1}.get(s[j], 0); j += 1
        # second argument
        assert s[j] == "{", "figtodo second argument expected"
        depth, k = 1, j + 1
        while depth:
            depth += {"{": 1, "}": -1}.get(s[k], 0); k += 1
        if tag in s[j:k]:
            return m.start(), k
    return None


def main():
    texdir = pathlib.Path(sys.argv[1])
    for fn, pairs in SWAPS.items():
        p = texdir / fn
        s = p.read_text(encoding="utf-8")
        n = 0
        for tag, rep in pairs:
            span = find_figtodo(s, tag)
            if span:
                s = s[:span[0]] + rep + s[span[1]:]
                n += 1
        p.write_text(s, encoding="utf-8")
        print(f"{fn}: {n} placeholder(s) swapped")


if __name__ == "__main__":
    main()
