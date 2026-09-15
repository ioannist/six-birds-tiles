#!/usr/bin/env python3
"""Build I09: repository-first Chair44 verification entry card."""
from __future__ import annotations

import hashlib
from io import BytesIO
import json
from pathlib import Path

from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps
import qrcode

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / "output" / "verify"
SOLID = ROOT / "solid" / "r44_solid.json"
PIN = ROOT / "reader" / "pin.json"
TILE = HERE / "source" / "feature_map" / "000090.png"

NAVY = "#1b2540"
NAVY2 = "#26325a"
CREAM = "#f4ecdf"
MUTED = "#c9cfe0"
GOLD = "#f3b53a"
CORAL = "#e8563f"
SKY = "#5aa9e6"
FONT_DIR = Path("/usr/share/fonts/truetype/dejavu")
FOOTER = "Ioannis Tsiokos · with ChatGPT Astra + Six Birds Theory · EmergenceCalculus.com/r44"
REPO_LABEL = "github.com/ioannist/six-birds-tiles"
REPO_URL = "https://github.com/ioannist/six-birds-tiles#check-it-for-yourself"
ENTRIES = [
    ("01", "ROTATE THE TILE", "Interactive 3D viewer · runs in your browser"),
    ("02", "RUN THE CHECKS", "Executable notebook · inspect outputs and mutations"),
    ("03", "ASK YOUR OWN AI", "Upload-ready reading bundle and executable package"),
    ("04", "READ THE PROOF", "Paper, theorem map and exact evidence locations"),
    ("05", "INSPECT THE SOLID", "Canonical rational JSON and display OBJ"),
]


def sha256(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def font(size: int, bold: bool = False, serif: bool = False) -> ImageFont.FreeTypeFont:
    family = "DejaVuSerif" if serif else "DejaVuSans"
    suffix = "-Bold.ttf" if bold else ".ttf"
    return ImageFont.truetype(str(FONT_DIR / (family + suffix)), max(7, size))


def fit_text(draw: ImageDraw.ImageDraw, copy: str, width: int, start: int,
             bold: bool = False, serif: bool = False, minimum: int = 8):
    size = start
    while size > minimum and draw.textlength(copy, font=font(size, bold, serif)) > width:
        size -= 1
    return font(size, bold, serif)


def background(size: tuple[int, int]) -> Image.Image:
    w, h = size
    top = Image.new("RGB", size, NAVY)
    bottom = Image.new("RGB", size, NAVY2)
    gradient = Image.linear_gradient("L").resize(size)
    canvas = Image.composite(bottom, top, gradient).convert("RGBA")
    glow = Image.new("RGBA", size, (0, 0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse((int(w * .45), -int(h * .25), int(w * 1.15), int(h * .7)),
               fill=(90, 169, 230, 24))
    return Image.alpha_composite(canvas, glow.filter(ImageFilter.GaussianBlur(max(25, w // 10))))


def tile_image() -> Image.Image:
    image = Image.open(TILE).convert("RGBA")
    box = image.getchannel("A").getbbox()
    assert box
    return image.crop(box)


def place_tile(canvas: Image.Image, box: tuple[int, int, int, int]) -> None:
    x0, y0, x1, y1 = box
    item = ImageOps.contain(tile_image(), (x1 - x0, y1 - y0), Image.Resampling.LANCZOS)
    x = x0 + (x1 - x0 - item.width) // 2
    y = y0 + (y1 - y0 - item.height) // 2
    shadow_alpha = item.getchannel("A").filter(ImageFilter.GaussianBlur(max(4, item.width // 35)))
    shadow = Image.new("RGBA", item.size, (3, 8, 20, 0))
    shadow.putalpha(shadow_alpha.point(lambda value: value * 90 // 255))
    canvas.alpha_composite(shadow, (x + item.width // 35, y + item.height // 30))
    canvas.alpha_composite(item, (x, y))


def qr_image(size: int) -> Image.Image:
    qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M,
                       box_size=8, border=3)
    qr.add_data(REPO_URL)
    qr.make(fit=True)
    return qr.make_image(fill_color=NAVY, back_color=CREAM).convert("RGB").resize(
        (size, size), Image.Resampling.NEAREST).convert("RGBA")


def entry(draw: ImageDraw.ImageDraw, box: tuple[int, int, int, int], number: str,
          title: str, detail: str, scale: float, compact: bool = False) -> None:
    x0, y0, x1, y1 = box
    radius = round((13 if compact else 16) * scale)
    draw.rounded_rectangle(box, radius=radius, fill=CREAM, outline=GOLD,
                           width=max(2, round(2 * scale)))
    badge = (x0 + round(15 * scale), y0 + round(14 * scale),
             x0 + round((65 if compact else 73) * scale), y1 - round(14 * scale))
    draw.rounded_rectangle(badge, radius=round(9 * scale), fill=NAVY)
    draw.text(((badge[0] + badge[2]) // 2, (badge[1] + badge[3]) // 2), number,
              font=font(round((15 if compact else 18) * scale), True), fill=GOLD, anchor="mm")
    tx = badge[2] + round(18 * scale)
    title_y = y0 + round((15 if compact else 17) * scale)
    draw.text((tx, title_y), title,
              font=font(round((15 if compact else 18) * scale), True), fill=NAVY)
    detail_y = y0 + round((42 if compact else 48) * scale)
    draw.text((tx, detail_y), detail,
              font=fit_text(draw, detail, x1 - tx - round(14 * scale),
                            round((12 if compact else 14) * scale)), fill="#596176")


def build_portrait(output: Path) -> None:
    w, h = 1080, 1350
    canvas = background((w, h))
    draw = ImageDraw.Draw(canvas)
    margin = 58
    title = "VERIFY CHAIR44 YOURSELF"
    draw.text((margin, 50), title,
              font=fit_text(draw, title, w - 2 * margin, 55, True, True), fill=CREAM)
    draw.text((margin, 122), "Five ways to inspect the shape, computation and proof.",
              font=fit_text(draw, "Five ways to inspect the shape, computation and proof.",
                            w - 2 * margin, 23), fill=MUTED)
    draw.rounded_rectangle((margin, 172, w - margin, 425), radius=20,
                           fill="#202d4d", outline="#405276", width=2)
    place_tile(canvas, (70, 180, 455, 416))
    draw.text((470, 212), "START WHERE YOU LIKE", font=font(20, True), fill=GOLD)
    draw.text((470, 254), "See it. Run it. Challenge it.", font=font(24, True), fill=CREAM)
    draw.multiline_text((470, 304),
                        "Every path leads back to the same\npinned solid, paper and evidence.",
                        font=font(18), fill=MUTED, spacing=8)
    draw.text((470, 386), "Exact tile · feature colours are annotations",
              font=font(13), fill=SKY)

    y = 457
    row_h, gap = 102, 13
    for item in ENTRIES:
        entry(draw, (margin, y, w - margin, y + row_h), *item, 1.0)
        y += row_h + gap

    cta_top = 1045
    draw.rounded_rectangle((margin, cta_top, w - margin, 1215), radius=18,
                           fill=NAVY2, outline=GOLD, width=2)
    qr = qr_image(128)
    canvas.alpha_composite(qr, (w - margin - 148, cta_top + 20))
    draw.text((margin + 25, cta_top + 28), "OPEN THE REPOSITORY", font=font(18, True), fill=GOLD)
    draw.text((margin + 25, cta_top + 70), REPO_LABEL,
              font=fit_text(draw, REPO_LABEL, 670, 24, True), fill=CREAM)
    draw.text((margin + 25, cta_top + 112),
              "Viewer, notebook, AI bundle, paper and solid are collected here.",
              font=fit_text(draw,
                            "Viewer, notebook, AI bundle, paper and solid are collected here.",
                            680, 14), fill=MUTED)
    draw.text((margin + 25, cta_top + 140), "These tools help you audit the claim; they add no evidence.",
              font=fit_text(draw, "These tools help you audit the claim; they add no evidence.",
                            680, 14), fill=MUTED)

    footer_y = 1308
    draw.line((margin, footer_y - 26, w - margin, footer_y - 26), fill="#405276", width=1)
    draw.text((margin, footer_y), FOOTER,
              font=fit_text(draw, FOOTER, w - 2 * margin, 13), fill=MUTED, anchor="ls")
    output.parent.mkdir(parents=True, exist_ok=True)
    canvas.convert("RGB").save(output, optimize=True)


def build_wide(output: Path) -> None:
    w, h = 1200, 630
    canvas = background((w, h))
    draw = ImageDraw.Draw(canvas)
    margin = 45
    draw.text((margin, 38), "VERIFY CHAIR44 YOURSELF",
              font=fit_text(draw, "VERIFY CHAIR44 YOURSELF", 410, 43, True, True), fill=CREAM)
    draw.text((margin, 94), "See it. Run it. Challenge the proof.", font=font(20), fill=MUTED)
    place_tile(canvas, (45, 138, 465, 440))
    draw.rounded_rectangle((48, 435, 455, 500), radius=12, fill=CREAM, outline=GOLD, width=2)
    draw.text((251, 458), "EXACT SOLID · ANNOTATED VIEW", font=font(14, True), fill=NAVY, anchor="ma")

    x0, x1 = 500, w - margin
    y, row_h, gap = 38, 82, 9
    for item in ENTRIES:
        entry(draw, (x0, y, x1, y + row_h), *item, 1.0, compact=True)
        y += row_h + gap

    qr = qr_image(92)
    canvas.alpha_composite(qr, (x0, 507))
    draw.text((x0 + 112, 526), "OPEN THE REPOSITORY", font=font(14, True), fill=GOLD)
    draw.text((x0 + 112, 553), REPO_LABEL,
              font=fit_text(draw, REPO_LABEL, 470, 19, True), fill=CREAM)
    draw.text((x0 + 112, 578), "One pinned route to every reader utility.", font=font(13), fill=MUTED)
    footer_y = 598
    draw.line((margin, footer_y - 16, 455, footer_y - 16), fill="#405276", width=1)
    draw.text((margin, footer_y + 14), FOOTER,
              font=fit_text(draw, FOOTER, 410, 10), fill=MUTED, anchor="ls")
    output.parent.mkdir(parents=True, exist_ok=True)
    canvas.convert("RGB").save(output, optimize=True)


def main() -> None:
    pin = json.loads(PIN.read_text())
    assert sha256(SOLID) == pin["canonical_sha256"]["solid/r44_solid.json"]
    outputs = [OUT / "verify_chair44_portrait_1080x1350.png",
               OUT / "verify_chair44_link_1200x630.png"]
    build_portrait(outputs[0])
    build_wide(outputs[1])
    receipt = {
        "asset": "I09 — Verify Chair44 yourself",
        "source_commit": pin["source_commit"],
        "canonical_solid_sha256": sha256(SOLID),
        "tile_render_sha256": sha256(TILE),
        "repository_target": REPO_URL,
        "hosted_links": "Deferred; this version routes all five paths through the repository.",
        "outputs": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size,
                                                    "sha256": sha256(path)}
                    for path in outputs},
    }
    (OUT / "verify_card_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
