#!/usr/bin/env bash

set -u
set -o pipefail

project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$project_dir" || exit 2

echo "POSITIVE BUILD: lake build"
build_output=$(mktemp)
if ! lake build >"$build_output" 2>&1; then
  cat "$build_output" >&2
  rm -f "$build_output"
  echo "POSITIVE BUILD FAILED; must-fail results are meaningless" >&2
  exit 2
fi
rm -f "$build_output"
echo "POSITIVE BUILD: PASS"

failures=0
discharge_build_passed=0
echo "DISCHARGE BUILD: lake build R44Discharge"
discharge_build_output=$(mktemp)
if ! lake build R44Discharge >"$discharge_build_output" 2>&1; then
  cat "$discharge_build_output" >&2
  rm -f "$discharge_build_output"
  echo "DISCHARGE BUILD FAILED; admission counting cannot substitute for compilation" >&2
  exit 2
fi
rm -f "$discharge_build_output"
discharge_build_passed=1
echo "DISCHARGE BUILD: PASS"

discharge_diff_audit_passed=0
if scripts/discharge_diff_audit.sh; then
  discharge_diff_audit_passed=1
else
  failures=$((failures + 1))
fi

discharge_audit_passed=0
discharge_output=$(mktemp)
if python3 - R44/Discharge R44.lean >"$discharge_output" 2>&1 <<'PY'
import re
import sys
from pathlib import Path

discharge_dir = Path(sys.argv[1])
root_file = Path(sys.argv[2])
sources = sorted(discharge_dir.glob("*.lean"))
# Phase F is closed: an empty Discharge source set is now the expected state.
# [compile-fix: exchange 7 promotes the complete admission-free closure]


def code_without_comments_or_strings(text: str) -> str:
    out = []
    i = 0
    block_depth = 0
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            newline = text.find("\n", i)
            if newline == -1:
                out.extend(" " * (len(text) - i))
                break
            out.extend(" " * (newline - i))
            out.append("\n")
            i = newline + 1
        elif text.startswith("/-", i):
            block_depth = 1
            out.extend("  ")
            i += 2
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    out.extend("  ")
                    i += 2
                elif text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if block_depth:
        raise SystemExit("DISCHARGE AUDIT: FAIL (unterminated block comment)")
    return "".join(out)


executable_sorries = 0
marked_sorries = 0
for source in sources:
    text = source.read_text()
    code = code_without_comments_or_strings(text)
    executable_sorries += len(re.findall(r"(?<![\w'])sorry(?![\w'])", code))
    marked_sorries += len(re.findall(r"(?m)^\s*(?:--|/--) SORRY:", text))

if executable_sorries != marked_sorries:
    raise SystemExit(
        "DISCHARGE SORRY AUDIT: FAIL "
        f"(executable={executable_sorries}, marked={marked_sorries})"
    )
if executable_sorries != 0:
    raise SystemExit(
        "DISCHARGE SORRY AUDIT: FAIL "
        f"(Phase F closed but executable={executable_sorries})"
    )
print(
    "DISCHARGE SORRY AUDIT: PASS "
    f"(executable={executable_sorries}, marked={marked_sorries})"
)

project_dir = root_file.parent
pending = ["R44"]
visited = set()
discharge_imports = set()
while pending:
    module = pending.pop()
    if module in visited:
        continue
    visited.add(module)
    path = project_dir / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        if module.startswith("R44."):
            raise SystemExit(
                f"R44 IMPORT CLOSURE: FAIL (missing local module {module})"
            )
        continue
    code = code_without_comments_or_strings(path.read_text())
    for imported in re.findall(r"(?m)^\s*import\s+([A-Za-z0-9_'.]+)", code):
        if imported.startswith("R44.Discharge"):
            discharge_imports.add(imported)
        imported_path = project_dir / (imported.replace(".", "/") + ".lean")
        if imported == "R44" or imported_path.is_file():
            pending.append(imported)

if discharge_imports:
    raise SystemExit(
        "R44 IMPORT CLOSURE: FAIL (contains "
        + ", ".join(sorted(discharge_imports))
        + ")"
    )
print(
    "R44 IMPORT CLOSURE: PASS "
    f"({len(visited)} local modules; no R44.Discharge modules)"
)
PY
then
  cat "$discharge_output"
  discharge_audit_passed=1
else
  cat "$discharge_output" >&2
  failures=$((failures + 1))
fi
rm -f "$discharge_output"

mapfile -d '' negative_files < <(find negative -type f -print0 | sort -z)
negative_total=${#negative_files[@]}
negative_passed=0

if (( negative_total == 0 )); then
  echo "NEGATIVE CONTROLS: FAIL (negative/ contains no files)" >&2
  failures=$((failures + 1))
fi

for file in "${negative_files[@]}"; do
  expected=$(sed -n 's/^-- EXPECT: //p' "$file" | head -n 1)
  output=$(mktemp)

  lake env lean -j 4 "$file" >"$output" 2>&1
  status=$?

  if (( status == 126 || status == 127 )); then
    echo "NEGATIVE CONTROL: FAIL $file (Lean executable unavailable; exit $status)" >&2
    cat "$output" >&2
    failures=$((failures + 1))
  elif grep -Eq "unknown module prefix|invalid import|failed to resolve import|object file .* does not exist" "$output"; then
    echo "NEGATIVE CONTROL: FAIL $file (import failure)" >&2
    cat "$output" >&2
    failures=$((failures + 1))
  elif [[ -z "$expected" ]]; then
    echo "NEGATIVE CONTROL: FAIL $file (missing -- EXPECT: header)" >&2
    cat "$output" >&2
    failures=$((failures + 1))
  elif (( status == 0 )); then
    echo "NEGATIVE CONTROL: FAIL $file (unexpected exit 0; expected: $expected)" >&2
    cat "$output" >&2
    failures=$((failures + 1))
  elif ! grep -Fq -- "$expected" "$output"; then
    echo "NEGATIVE CONTROL: FAIL $file (exit $status without expected diagnostic: $expected)" >&2
    cat "$output" >&2
    failures=$((failures + 1))
  else
    echo "NEGATIVE CONTROL: PASS $file (exit $status; matched: $expected)"
    negative_passed=$((negative_passed + 1))
  fi
  rm -f "$output"
done

scope_passed=0
scope_output=$(mktemp)
lake env lean -j 4 R44/ScopeRegressions.lean >"$scope_output" 2>&1
scope_status=$?
if (( scope_status == 0 )); then
  echo "POSITIVE SCOPE: PASS R44/ScopeRegressions.lean"
  scope_passed=1
else
  echo "POSITIVE SCOPE: FAIL R44/ScopeRegressions.lean (exit $scope_status)" >&2
  cat "$scope_output" >&2
  failures=$((failures + 1))
fi
rm -f "$scope_output"

if (( failures == 0 )); then
  echo "CONTROLS: PASS (build=1/1, discharge_build=$discharge_build_passed/1, discharge_diff=$discharge_diff_audit_passed/1, discharge_audit=$discharge_audit_passed/1, admissions=0, negative=$negative_passed/$negative_total, scope=$scope_passed/1)"
  exit 0
fi

echo "CONTROLS: FAIL (build=1/1, discharge_build=$discharge_build_passed/1, discharge_diff=$discharge_diff_audit_passed/1, discharge_audit=$discharge_audit_passed/1, negative=$negative_passed/$negative_total, scope=$scope_passed/1, failures=$failures)" >&2
exit 1
