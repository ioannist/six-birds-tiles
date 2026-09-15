#!/usr/bin/env bash

set -u
set -o pipefail

project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
repo_dir=$(cd "$project_dir/../.." && pwd)

python3 - "$repo_dir" <<'PY'
import difflib
import sys
import zipfile
from pathlib import Path

repo_dir = Path(sys.argv[1])
discharge_dir = repo_dir / "lean/R44/R44/Discharge"
proved_dir = repo_dir / "lean/R44/R44/Proved"
exchange2_archive = repo_dir / "proof/external_lean/F1_exchange2/r44_F1_exchange2_discharge.zip"
exchange3_archive = repo_dir / "proof/external_lean/F2_exchange3/r44_F2_exchange3_discharge.zip"
exchange4_archive = repo_dir / "proof/external_lean/F3_exchange4/r44_F3_exchange4_discharge.zip"
exchange5_archive = repo_dir / "proof/external_lean/F4_exchange5/r44_F4_exchange5_discharge.zip"
exchange6_archive = repo_dir / "proof/external_lean/F5_exchange6/r44_exchange6_bridges.zip"
exchange7_archive = repo_dir / "proof/external_lean/F6_exchange7/r44_exchange7_native_interpretation.zip"
complete_archive = repo_dir / "proof/external_lean/r44_F1_complete_dihedral_list_draft.zip"
member_prefix = "lean/R44/R44/Discharge/"

exchange2_files = [
    "NativeGeometry.lean",
    "CarrierSymmetries.lean",
    "RetainedCoreOverlap.lean",
    "CarrierFeatureFrameReduction.lean",
    "CircularConeSolidAngle.lean",
]
exchange3_files = [
    "TubeCalculus.lean",
    "PerTubeHomeomorphisms.lean",
    "FeatureTubeMapsGlue.lean",
    "FeatureTubeMapCarriesCarrier.lean",
    "FeatureLocalCharts.lean",
    "FeatureCircularConeContainment.lean",
    "MetricCarrierRecovery.lean",
    "PlanarAreaCarrierRecovery.lean",
]
exchange4_files = [
    "CompactCongruent.lean",
    "CompanionPoseDiscrete.lean",
    "ConeSectorBudgets.lean",
    "ConnectedFeatureCompanion.lean",
    "CubicFrameAlgebra.lean",
    "FeatureContainmentRigidity.lean",
    "FeatureGraphTopology.lean",
    "GenericFeaturePartner.lean",
    "HashListSemantics.lean",
    "MateCensusSemantics.lean",
    "MeshSemantics.lean",
    "NativeMateGeometry.lean",
    "PolyhedralGerms.lean",
    "PyramidGeometry.lean",
    "SectorArithmetic.lean",
    "TentTangentCharts.lean",
]
exchange5_files = [
    "AssemblyCollarData.lean",
    "BaselineComponentCoversGrid.lean",
    "CarrierCoreCover.lean",
    "CompanionCollisionSemantics.lean",
    "ComponentSolidsCover.lean",
    "ConcreteCompanions.lean",
    "GenericBoundaryLabels.lean",
    "GenericFeaturePartner.lean",
    "MeshSemantics.lean",
    "NativeDihedralSectors.lean",
    "OnlyRegisteredMates.lean",
    "PolyhedralConeMeasure.lean",
    "RegisteredCellGeometry.lean",
    "RegisteredComponentGeometry.lean",
    "RetainedBoxGeometry.lean",
    "SeparatedHomeomorphismGluing.lean",
    "SmallCollarRealization.lean",
    "TubeSiteGeometry.lean",
    "UnrestrictedAlignment.lean",
    "WedgeVolume.lean",
]
exchange6_files = [
    "AssemblyCollarData.lean",
    "AssemblyCollarIncidence.lean",
    "FiniteEdgeExceptions.lean",
    "GenericBoundaryLabels.lean",
    "NativeBoundaryStrata.lean",
    "NativeDihedralSectors.lean",
    "PairedCollarMaps.lean",
    "PanelIncidence.lean",
    "PlanarSectorArea.lean",
    "TangentIsometry.lean",
    "TentMeridianReduction.lean",
]
exchange7_files = [
    "AngularMeridianCore.lean",
    "CanonicalTentStrata.lean",
    "CarrierBoundaryStrata.lean",
    "CarrierCoordinateStates.lean",
    "ElementarySectorGeometry.lean",
    "MeshChartIncidence.lean",
    "MeshChartInterpretation.lean",
    "NativeBoundaryLocal.lean",
    "NativeBoundaryStrata.lean",
    "NativeDihedralSectors.lean",
    "NativeExceptionalVertices.lean",
    "NativeFeatureMeridians.lean",
    "OrdinaryMeridians.lean",
]
expected_files = set(
    exchange2_files + exchange3_files + exchange4_files + exchange5_files + exchange6_files
    + exchange7_files
    + ["CompleteDihedralList.lean"]
)
# [compile-fix: exchange 7 discharges the complete admission-free closure]
promoted_files = expected_files
remaining_files = set()

actual_remaining = {path.name for path in discharge_dir.glob("*.lean")}
actual_promoted = {path.name for path in proved_dir.glob("*.lean")}
if actual_remaining != remaining_files or actual_promoted != promoted_files:
    missing = sorted(
        (remaining_files - actual_remaining) | (promoted_files - actual_promoted)
    )
    extra = sorted(
        (actual_remaining - remaining_files) | (actual_promoted - promoted_files)
    )
    print(
        "DISCHARGE DIFF AUDIT: FAIL "
        f"(missing={missing or 'none'}, extra={extra or 'none'})",
        file=sys.stderr,
    )
    raise SystemExit(1)

for archive in (
    exchange2_archive,
    exchange3_archive,
    exchange4_archive,
    exchange5_archive,
    exchange6_archive,
    exchange7_archive,
    complete_archive,
):
    if not archive.is_file():
        print(f"DISCHARGE DIFF AUDIT: FAIL (missing delivery {archive})", file=sys.stderr)
        raise SystemExit(1)


def delivery_text(filename: str) -> str:
    if filename == "CompleteDihedralList.lean":
        archive = complete_archive
    elif filename in exchange7_files:
        archive = exchange7_archive
    elif filename in exchange6_files:
        archive = exchange6_archive
    elif filename in exchange5_files:
        archive = exchange5_archive
    elif filename in exchange4_files:
        archive = exchange4_archive
    elif filename in exchange3_files:
        archive = exchange3_archive
    else:
        archive = exchange2_archive
    member = member_prefix + filename
    try:
        with zipfile.ZipFile(archive) as delivery:
            return delivery.read(member).decode()
    except (KeyError, UnicodeDecodeError, zipfile.BadZipFile) as error:
        print(
            f"DISCHARGE DIFF AUDIT: FAIL {filename} "
            f"(cannot read {archive.relative_to(repo_dir)}::{member}: {error})",
            file=sys.stderr,
        )
        raise SystemExit(1)


def current_path(filename: str) -> Path:
    return (proved_dir if filename in promoted_files else discharge_dir) / filename


def block_coverage(filename: str, lines: list[str]) -> list[bool]:
    covered = [False] * len(lines)
    active = False
    for index, line in enumerate(lines):
        begins = "-- [compile-fix begin:" in line
        ends = "-- [compile-fix end]" in line
        if begins:
            if active:
                print(
                    f"DISCHARGE DIFF AUDIT: FAIL {filename}:{index + 1} "
                    "(nested compile-fix block)",
                    file=sys.stderr,
                )
                raise SystemExit(1)
            active = True
        covered[index] = active or begins or ends
        if ends:
            if not active:
                print(
                    f"DISCHARGE DIFF AUDIT: FAIL {filename}:{index + 1} "
                    "(compile-fix end without begin)",
                    file=sys.stderr,
                )
                raise SystemExit(1)
            active = False
    if active:
        print(
            f"DISCHARGE DIFF AUDIT: FAIL {filename} (unterminated compile-fix block)",
            file=sys.stderr,
        )
        raise SystemExit(1)
    return covered


failures = []
passed = 0
for filename in sorted(expected_files):
    old_lines = delivery_text(filename).splitlines()
    new_lines = current_path(filename).read_text().splitlines()
    covered = block_coverage(filename, new_lines)
    changed_indices = []
    all_changed_indices = []
    unbracketed_deletions = []
    matcher = difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
    for tag, old_start, old_end, new_start, new_end in matcher.get_opcodes():
        if tag in {"replace", "insert"}:
            all_changed_indices.extend(range(new_start, new_end))
            # A compile-fix marker labels its whole contiguous diff hunk; larger
            # proof-method replacements need not repeat the marker on every line.
            hunk_marked = any(
                "-- [compile-fix" in new_lines[index] or covered[index]
                for index in range(new_start, new_end)
            )
            if not hunk_marked:
                changed_indices.extend(range(new_start, new_end))
        elif tag == "delete":
            before_is_bracketed = new_start > 0 and covered[new_start - 1]
            after_is_bracketed = new_start < len(new_lines) and covered[new_start]
            if not (before_is_bracketed or after_is_bracketed):
                unbracketed_deletions.append((old_start + 1, old_end))

    changed_content = [index for index in changed_indices if new_lines[index].strip()]
    all_changed_content = [
        index for index in all_changed_indices if new_lines[index].strip()
    ]
    unmarked = [
        index
        for index in changed_content
        if "-- [compile-fix" not in new_lines[index] and not covered[index]
    ]
    if unmarked or unbracketed_deletions:
        failures.extend((filename, index + 1, new_lines[index].strip()) for index in unmarked)
        failures.extend(
            (filename, f"delivery:{start}-{end}", "deleted outside a compile-fix block")
            for start, end in unbracketed_deletions
        )
        print(
            f"DISCHARGE DIFF AUDIT: FAIL {filename} "
            f"(unmarked current lines={len(unmarked)}, "
            f"unbracketed deletion groups={len(unbracketed_deletions)})",
            file=sys.stderr,
        )
    else:
        print(
            f"DISCHARGE DIFF AUDIT: PASS {filename} "
            f"(changed content lines={len(all_changed_content)})"
        )
        passed += 1

if failures:
    for filename, location, content in failures:
        print(f"  {filename}:{location}: {content}", file=sys.stderr)
    print(
        f"DISCHARGE DIFF AUDIT: FAIL ({passed}/{len(expected_files)} files)",
        file=sys.stderr,
    )
    raise SystemExit(1)

print(f"DISCHARGE DIFF AUDIT: PASS ({passed}/{len(expected_files)} files)")
PY
