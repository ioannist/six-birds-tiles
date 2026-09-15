#!/usr/bin/env python3
"""Assemble I11 from the approved 4:5 Chair44 campaign assets."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / "output" / "carousel"
PIN = ROOT / "reader" / "pin.json"
SOLID = ROOT / "solid" / "r44_solid.json"
FONT = Path("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf")
GOLD = "#f3b53a"
NAVY = "#1b2540"
CREAM = "#f4ecdf"

SOURCES = [
    ("01_object_and_claim", HERE / "output" / "hero" / "hero_portrait_1080x1350.png"),
    ("02_periodic_control", HERE / "output" / "comparison" / "comparison_portrait_1080x1350.png"),
    ("03_hierarchy_argument", HERE / "output" / "period_argument" / "why_translation_period_fails_portrait_1080x1350.png"),
    ("04_verify_it_yourself", HERE / "output" / "verify" / "verify_chair44_portrait_1080x1350.png"),
]


def sha256(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def badge(image: Image.Image, index: int) -> None:
    draw = ImageDraw.Draw(image, "RGBA")
    box = (957, 18, 1048, 57)
    draw.rounded_rectangle(box, radius=10, fill=(27, 37, 64, 235),
                           outline=GOLD, width=2)
    draw.text(((box[0] + box[2]) // 2, (box[1] + box[3]) // 2), f"{index} / 4",
              font=ImageFont.truetype(str(FONT), 16), fill=CREAM, anchor="mm")


def main() -> None:
    pin = json.loads(PIN.read_text())
    assert sha256(SOLID) == pin["canonical_sha256"]["solid/r44_solid.json"]
    OUT.mkdir(parents=True, exist_ok=True)
    outputs = []
    cards = []
    for index, (stem, source) in enumerate(SOURCES, 1):
        assert source.exists()
        image = Image.open(source).convert("RGB")
        assert image.size == (1080, 1350)
        badge(image, index)
        output = OUT / f"chair44_carousel_{stem}_1080x1350.png"
        image.save(output, optimize=True)
        outputs.append(output)
        cards.append(image)

    # Review contact sheet only; individual files remain publication masters.
    contact = Image.new("RGB", (1620, 2025), "#11182a")
    for i, card in enumerate(cards):
        thumb = card.resize((792, 990), Image.Resampling.LANCZOS)
        contact.paste(thumb, (12 + (i % 2) * 804, 12 + (i // 2) * 1002))
    contact_path = OUT / "chair44_carousel_contact_sheet_1620x2025.png"
    contact.save(contact_path, optimize=True)

    receipt = {
        "asset": "I11 — four-card carousel",
        "source_commit": pin["source_commit"],
        "canonical_solid_sha256": sha256(SOLID),
        "sequence": [stem for stem, _ in SOURCES],
        "safe_zone": "Critical copy remains at least 48 px from each 1080×1350 edge; sequence badge is inset 18 px as platform furniture.",
        "sources": {str(path.relative_to(ROOT)): sha256(path) for _, path in SOURCES},
        "outputs": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size,
                                                    "sha256": sha256(path)}
                    for path in outputs + [contact_path]},
    }
    (OUT / "carousel_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
