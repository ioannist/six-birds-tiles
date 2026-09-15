#!/usr/bin/env bash
# Full-repo zip for the external final review (< 100 MB): everything the theorem rests on, from the
# committed tree, excluding historical trees and build products. Usage: scripts/make_final_review_zip.sh <out.zip>
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; OUT="${1:?output zip path}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
git -C "$ROOT" archive --format=tar HEAD | tar -x -C "$tmp"
rm -rf "$tmp/history" "$tmp/archive" "$tmp/.codex" "$tmp/provenance/six-birds-tiles_checkpoint350.zip"
( cd "$tmp" && python3 verify/replay.py > /dev/null && echo "replay PASS inside archive" )
( cd "$tmp" && python3 -m unittest discover simulations/tests > /dev/null 2>&1 && echo "simulation tests PASS inside archive" )
rm -rf "$tmp/verify/packets/"*/results/*.replay.log "$tmp"/simulations/tests/_generated "$tmp"/simulations/generated 2>/dev/null || true
cat > "$tmp/ZIP_CONTENTS.md" <<'NOTE'
This archive is the six-birds-tiles repository at the commit named in COMMIT.txt, minus: history/ (the
350-step construction cascade and external dialogue), archive/ (a retired search engine), .codex/
(agent dispatcher state) and the 28 MB checkpoint-350 workspace snapshot. Nothing the theorem, its
certificates, checkers, Lean development, simulations or figures depend on has been removed. Lean
build products and the Mathlib package tree are not included; lean/R44/README.md says how to build.
NOTE
git -C "$ROOT" rev-parse HEAD > "$tmp/COMMIT.txt"
( cd "$tmp" && zip -qr "$OUT" . ) ; unzip -tq "$OUT" | tail -1; ls -la "$OUT"
