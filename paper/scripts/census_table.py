#!/usr/bin/env python3
"""Table 2 (FIGURES.md): the censuses, read from the certificates and the packet results
that the replay checks (certificates/candidate_certificate.json,
certificates/companion_collision_certificate.json,
verify/packets/r44_unrestricted_alignment/results/alignment_verification.json) and from the
JSON output of verify/substitution_modular_coincidence.py (run here, read-only). The numbers
are those the Lean theorems certify; this script only tabulates them."""
import argparse
import json
import os
import subprocess
import sys

from _texutil import ROOT, common_args, finish, num, write_rows


def load(rel):
    return json.load(open(os.path.join(ROOT, rel), encoding="utf-8"))


def main():
    ap = common_args(argparse.ArgumentParser(description=__doc__), lean=False)
    args = ap.parse_args()
    c = load("certificates/candidate_certificate.json")
    cc = load("certificates/companion_collision_certificate.json")
    al = load("verify/packets/r44_unrestricted_alignment/results/alignment_verification.json")
    mates = al["complete_feature_mates"]
    proc = subprocess.run([sys.executable, os.path.join(ROOT, "verify", "substitution_modular_coincidence.py")],
                          check=True, capture_output=True, text=True)
    sub = json.loads(proc.stdout.strip().splitlines()[-1])
    frames = {json.dumps(lc[0]) for lc in c["legal_contacts"]}
    n_pairs = len(c["parents"]) * (len(c["parents"]) - 1) // 2
    conflicts = n_pairs - len(c["compatible_parent_pairs"])
    checks = [
        len(c["raw_contacts"]) == 2388, len(c["legal_contacts"]) == 44, len(frames) == 19,
        len(c["orientation_group"]) == 24, len(c["solutions"]) == 33,
        len(c["central_passed"]) == 14, len(c["central_dead"]) == 18, len(c["central_wrong"]) == 0,
        conflicts == 28, len(c["macro_candidates"]) == 697, c["macro_nonoverlap"] == 116,
        len(c["macro_legal"]) == 44, c["coarse_equals_fine"] is True, c["macro_alignment_even"] is True,
        mates["raw"] == 6862, mates["isolated"] == 5317, mates["survivors"] == 44,
        mates["rejected_with_exhaustive_companion_collision"] == cc["rejected_disjoint_mates"] == 5273,
        mates["companion_options_checked"] == cc["companion_collision_tests"] == 299975,
        mates["same_as_registered_atlas_as_sets"] is True,
        sub["labels"] == 168, sub["column_sum"] == 8, sub["least_primitive_exponent_N"] == 3,
        sub["least_coincidence_depth_M"] == 3, sub["coincidence_address_a"] == [0, 0, 2],
        sub["coincidence_label_i"] == 78, sub["status"] == "PASS",
        c["contact_state_count"] == 30 if "contact_state_count" in c else len(c["contact_states"]) == 30,
        len(c["signed_rows"]) == 372, len(c["balanced_components"]) == 12,
    ]
    rows = [
        ["contact closure: internal face contacts $\\to$ closed states; sign equations; balanced components",
         f"${c['closure_counts'][0]}\\to{len(c['contact_states'])}$; ${len(c['signed_rows'])}$; ${len(c['balanced_components'])}$"],
        ["shell poses in $48$ frames $\\to$ legal contacts (the atlas); distinct rotations; group generated",
         f"${num(len(c['raw_contacts']))}\\to{len(c['legal_contacts'])}$; ${len(frames)}$; ${len(c['orientation_group'])}$"],
        ["first shells; outer-root completions found / impossible; parent conflicts",
         f"${len(c['solutions'])}$; ${len(c['central_passed'])}/{len(c['central_dead'])}$; ${conflicts}$"],
        ["parent contacts: candidates $\\to$ disjoint $\\to$ legal; halved $=$ fine atlas",
         f"${len(c['macro_candidates'])}\\to{c['macro_nonoverlap']}\\to{len(c['macro_legal'])}$; yes"],
        ["complete-feature mate poses $\\to$ isolated $\\to$ survivors",
         f"${num(mates['raw'])}\\to{num(mates['isolated'])}\\to{mates['survivors']}$"],
        ["rejected isolated poses; companion-option collisions checked",
         f"${num(mates['rejected_with_exhaustive_companion_collision'])}$; ${num(mates['companion_options_checked'])}$"],
        ["substitution labels; column sum; least primitive exponent $N$; coincidence depth $M$, address $a$, label $i$",
         f"${sub['labels']}$; ${sub['column_sum']}$; ${sub['least_primitive_exponent_N']}$; "
         f"${sub['least_coincidence_depth_M']}$, $({','.join(str(x) for x in sub['coincidence_address_a'])})$, ${sub['coincidence_label_i']}$"],
    ]
    write_rows(args.out, "census_table", rows,
               "from certificates/*.json, the alignment packet results and substitution_modular_coincidence.py",
               colspec="L{0.6\\linewidth} l", header=["census", "count"])
    finish(all(checks), f"a census count differs from the certified values: {[i for i, k in enumerate(checks) if not k]}")


if __name__ == "__main__":
    main()
