#!/usr/bin/env bash
# Build the external-review zip from the committed tree (git archive HEAD), excluding history/ bulk and
# the retired engine; Mathlib build products are never in git. Usage: scripts/make_review_zip.sh <out.zip>
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# U5 extends the existing entry point; the single output.zip argument remains the legacy mode.
# Compact release: scripts/make_review_zip.sh --reader --out /absolute/output-directory
# Immutable-source development preview: add --preview (filenames and manifest say preview).
if [[ "${1:-}" == "--reader" ]]; then
  shift
  exec python3 "$ROOT/reader/build_package.py" "$@"
fi
OUT="${1:?output zip path (or --reader --out directory)}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
git -C "$ROOT" archive --format=tar HEAD | tar -x -C "$tmp"
rm -rf "$tmp/history" "$tmp/archive" "$tmp/.codex" "$tmp/provenance/sbt_papers"
( cd "$tmp" && python3 verify/replay.py > /dev/null && echo "replay PASS inside archive" )
rm -rf "$tmp/verify/packets/"*/results/*.replay.log 2>/dev/null || true
( cd "$tmp" && zip -qr "$OUT" . ) ; unzip -tq "$OUT" | tail -1; ls -la "$OUT"
