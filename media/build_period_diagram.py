#!/usr/bin/env python3
"""Build I08: the Chair44 period-halving argument diagram."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / "output" / "period_argument"
SOLID = ROOT / "solid" / "r44_solid.json"
PIN = ROOT / "reader" / "pin.json"
TILE = HERE / "source" / "feature_map" / "000090.png"
PARENT8 = HERE / "source" / "hierarchy" / "parent8" / "003600.png"
LEVEL64 = HERE / "source" / "hierarchy" / "level64" / "003810.png"

NAVY = "#1b2540"
NAVY2 = "#26325a"
CREAM = "#f4ecdf"
MUTED = "#c9cfe0"
GOLD = "#f3b53a"
CORAL = "#e8563f"
SKY = "#5aa9e6"
FONT_DIR = Path("/usr/share/fonts/truetype/dejavu")
FOOTER = "Ioannis Tsiokos · with ChatGPT Astra + Six Birds Theory · EmergenceCalculus.com/r44"


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


def lines(draw: ImageDraw.ImageDraw, copy: str, face, width: int) -> list[str]:
    words = copy.split()
    out, current = [], ""
    for word in words:
        trial = f"{current} {word}".strip()
        if current and draw.textlength(trial, font=face) > width:
            out.append(current)
            current = word
        else:
            current = trial
    if current:
        out.append(current)
    return out


def wrapped(draw: ImageDraw.ImageDraw, xy: tuple[int, int], copy: str, face,
            fill: str, width: int, spacing: int | None = None) -> int:
    rendered = lines(draw, copy, face, width)
    spacing = spacing if spacing is not None else max(3, face.size // 4)
    draw.multiline_text(xy, "\n".join(rendered), font=face, fill=fill, spacing=spacing)
    return len(rendered) * (face.size + spacing)


def field(size: tuple[int, int]) -> Image.Image:
    w, h = size
    top = Image.new("RGB", size, NAVY)
    bottom = Image.new("RGB", size, NAVY2)
    gradient = Image.linear_gradient("L").resize(size)
    canvas = Image.composite(bottom, top, gradient).convert("RGBA")
    glow = Image.new("RGBA", size, (0, 0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse((int(w * .45), -int(h * .12), int(w * 1.08), int(h * .62)),
               fill=(90, 169, 230, 20))
    return Image.alpha_composite(canvas, glow.filter(ImageFilter.GaussianBlur(max(30, w // 11))))


def crop_alpha(path: Path) -> Image.Image:
    image = Image.open(path).convert("RGBA")
    box = image.getchannel("A").getbbox()
    assert box
    return image.crop(box)


def place_contain(canvas: Image.Image, source: Image.Image,
                  box: tuple[int, int, int, int]) -> None:
    x0, y0, x1, y1 = box
    item = ImageOps.contain(source, (x1 - x0, y1 - y0), Image.Resampling.LANCZOS)
    x = x0 + (x1 - x0 - item.width) // 2
    y = y0 + (y1 - y0 - item.height) // 2
    shadow_alpha = item.getchannel("A").filter(ImageFilter.GaussianBlur(max(3, item.width // 35)))
    shadow = Image.new("RGBA", item.size, (5, 10, 24, 0))
    shadow.putalpha(shadow_alpha.point(lambda value: value * 85 // 255))
    canvas.alpha_composite(shadow, (x + max(2, item.width // 40), y + max(3, item.height // 35)))
    canvas.alpha_composite(item, (x, y))


def arrow(draw: ImageDraw.ImageDraw, start: tuple[int, int], end: tuple[int, int],
          fill: str, width: int) -> None:
    draw.line((*start, *end), fill=fill, width=width)
    x1, y1 = end
    direction = 1 if x1 >= start[0] else -1
    head = max(8, width * 3)
    draw.polygon([(x1, y1), (x1 - direction * head, y1 - head // 2),
                  (x1 - direction * head, y1 + head // 2)], fill=fill)


def hierarchy_strip(canvas: Image.Image, box: tuple[int, int, int, int], scale: float) -> None:
    draw = ImageDraw.Draw(canvas)
    x0, y0, x1, y1 = box
    radius = round(18 * scale)
    draw.rounded_rectangle(box, radius=radius, fill="#202d4d", outline="#405276",
                           width=max(2, round(2 * scale)))
    pad = round(24 * scale)
    draw.text((x0 + pad, y0 + pad), "THE FORCED HIERARCHY · EXACT FINITE PATCHES",
              font=font(round(19 * scale), True), fill=GOLD)
    cluster_note = "exact meshes · colours identify copies · cluster features are subpixel"
    draw.text((x1 - pad, y0 + pad + round(22 * scale)), cluster_note,
              font=fit_text(draw, cluster_note, round(430 * scale), round(12 * scale)),
              fill=MUTED, anchor="ra")
    sources = [crop_alpha(TILE), crop_alpha(PARENT8), crop_alpha(LEVEL64)]
    labels = [("1", "Chair44"), ("8", "one parent cluster"), ("64", "two levels")]
    inner_top = y0 + round(58 * scale)
    inner_bottom = y1 - round(18 * scale)
    cell_w = (x1 - x0 - 2 * pad) // 3
    for i, (source, (count, label)) in enumerate(zip(sources, labels)):
        cx0 = x0 + pad + i * cell_w
        cx1 = cx0 + cell_w
        place_contain(canvas, source, (cx0 + round(12 * scale), inner_top,
                                       cx1 - round(12 * scale), inner_bottom - round(35 * scale)))
        noun = "copy" if count == "1" else "copies"
        draw.text(((cx0 + cx1) // 2, inner_bottom), f"{count} {noun} · {label}",
                  font=font(round(14 * scale), i == 2), fill=CREAM, anchor="ms")
        if i < 2:
            arrow(draw, (cx1 - round(13 * scale), (inner_top + inner_bottom) // 2),
                  (cx1 + round(13 * scale), (inner_top + inner_bottom) // 2),
                  GOLD, max(2, round(3 * scale)))


def period_card(canvas: Image.Image, box: tuple[int, int, int, int], title: str,
                period: str, length_fraction: float, note: str, scale: float) -> None:
    draw = ImageDraw.Draw(canvas)
    x0, y0, x1, y1 = box
    draw.rounded_rectangle(box, radius=round(16 * scale), fill=CREAM, outline=GOLD,
                           width=max(2, round(2 * scale)))
    pad = round(20 * scale)
    draw.text((x0 + pad, y0 + pad), title, font=font(round(27 * scale), True, True), fill=NAVY)
    draw.text((x1 - pad, y0 + pad), "REGISTERED GRID", font=font(round(11 * scale), True),
              fill=CORAL, anchor="ra")
    gx0, gy0 = x0 + pad, y0 + round(65 * scale)
    gx1, gy1 = x1 - pad, y1 - round(70 * scale)
    grid_step = max(round(29 * scale), 14)
    for x in range(gx0, gx1 + 1, grid_step):
        draw.line((x, gy0, x, gy1), fill="#d6d0c7", width=max(1, round(scale)))
    for y in range(gy0, gy1 + 1, grid_step):
        draw.line((gx0, y, gx1, y), fill="#d6d0c7", width=max(1, round(scale)))
    cy = (gy0 + gy1) // 2
    start_x = gx0 + round(22 * scale)
    max_length = gx1 - gx0 - round(44 * scale)
    end_x = start_x + round(max_length * length_fraction)
    draw.ellipse((start_x - round(6 * scale), cy - round(6 * scale),
                  start_x + round(6 * scale), cy + round(6 * scale)), fill=NAVY)
    arrow(draw, (start_x, cy), (end_x, cy), CORAL, max(3, round(5 * scale)))
    draw.rounded_rectangle((start_x + round(8 * scale), cy - round(46 * scale),
                            end_x - round(5 * scale), cy - round(12 * scale)),
                           radius=round(8 * scale), fill=NAVY)
    draw.text(((start_x + end_x) // 2, cy - round(29 * scale)), period,
              font=font(round(18 * scale), True), fill=CREAM, anchor="mm")
    draw.text((x0 + pad, y1 - round(48 * scale)), note,
              font=fit_text(draw, note, x1 - x0 - 2 * pad, round(14 * scale), True),
              fill=NAVY)


def build(size: tuple[int, int], output: Path) -> None:
    w, h = size
    scale = w / 1080
    portrait = h > w * 1.12
    canvas = field(size)
    draw = ImageDraw.Draw(canvas)
    margin = round(52 * scale)
    title_size = round((53 if portrait else 48) * scale)
    title = "WHY A TRANSLATION PERIOD FAILS"
    draw.text((margin, round(48 * scale)), "WHY A TRANSLATION PERIOD FAILS",
              font=fit_text(draw, title, w - 2 * margin, title_size, True, True), fill=CREAM)
    subtitle = "The argument applies to every possible tiling by Chair44—not merely to a displayed patch."
    draw.text((margin, round(118 * scale)), subtitle,
              font=fit_text(draw, subtitle, w - 2 * margin, round(22 * scale)), fill=MUTED)
    badge_y = round(160 * scale)
    draw.rounded_rectangle((margin, badge_y, margin + round(355 * scale), badge_y + round(38 * scale)),
                           radius=round(10 * scale), fill=NAVY2, outline=GOLD,
                           width=max(1, round(2 * scale)))
    draw.text((margin + round(178 * scale), badge_y + round(19 * scale)),
              "ARGUMENT DIAGRAM · THEOREM, NOT SIMULATION",
              font=font(round(12 * scale), True), fill=GOLD, anchor="mm")

    if portrait:
        hierarchy_box = (margin, round(225 * scale), w - margin, round(545 * scale))
        cards_y0, cards_y1 = round(605 * scale), round(930 * scale)
        conclusion_y = round(985 * scale)
    else:
        hierarchy_box = (margin, round(205 * scale), w - margin, round(450 * scale))
        cards_y0, cards_y1 = round(485 * scale), round(730 * scale)
        conclusion_y = round(760 * scale)
    hierarchy_strip(canvas, hierarchy_box, scale)

    gap = round(18 * scale)
    card_w = (w - 2 * margin - 2 * gap) // 3
    cards = [
        ("T", "p", 1.0, "registration ⇒ p is an integer vector"),
        ("D(T)", "p / 2", .56, "unique parents + same rule"),
        ("D²(T)", "p / 4", .31, "coarsen again"),
    ]
    for i, item in enumerate(cards):
        x0 = margin + i * (card_w + gap)
        period_card(canvas, (x0, cards_y0, x0 + card_w, cards_y1), *item, scale)

    # Connect the logical steps without implying that the finite strip proves them.
    for i in (1, 2):
        x = margin + i * card_w + (i - .5) * gap
        draw.ellipse((x - round(15 * scale), (cards_y0 + cards_y1) // 2 - round(15 * scale),
                      x + round(15 * scale), (cards_y0 + cards_y1) // 2 + round(15 * scale)),
                     fill=GOLD)
        draw.text((x, (cards_y0 + cards_y1) // 2), "›", font=font(round(27 * scale), True),
                  fill=NAVY, anchor="mm")

    draw.text((margin, conclusion_y), "REPEAT FOR EVERY n", font=font(round(18 * scale), True), fill=GOLD)
    equation_y = conclusion_y + round(40 * scale)
    equation = "p / 2ⁿ is an integer vector for every n"
    draw.text((w // 2, equation_y), equation,
              font=fit_text(draw, equation, w - 2 * margin, round(38 * scale), True, True),
              fill=CREAM, anchor="ma")
    reasoning = "The only integer vector divisible by every power of two is p = 0."
    draw.text((w // 2, equation_y + round(62 * scale)), reasoning,
              font=fit_text(draw, reasoning, w - 2 * margin, round(22 * scale), True),
              fill=MUTED, anchor="ma")
    theorem_y = equation_y + round((112 if portrait else 100) * scale)
    theorem_height = round((78 if portrait else 62) * scale)
    draw.rounded_rectangle((margin, theorem_y, w - margin, theorem_y + theorem_height),
                           radius=round(13 * scale), fill=CORAL)
    theorem = "THEREFORE: NO TILING BY CHAIR44 HAS A NONZERO TRANSLATION PERIOD"
    draw.text((w // 2, theorem_y + theorem_height // 2), theorem,
              font=fit_text(draw, theorem, w - 2 * margin - round(30 * scale),
                            round(20 * scale), True), fill=CREAM, anchor="mm")
    note_y = theorem_y + round((100 if portrait else 84) * scale)
    note = "Required proof gates: global registration · unique translation-covariant parents · same-law coarsening"
    draw.text((w // 2, note_y), note,
              font=fit_text(draw, note, w - 2 * margin, round(15 * scale)),
              fill=MUTED, anchor="ma")

    footer_y = h - round(42 * scale)
    draw.line((margin, footer_y - round(27 * scale), w - margin, footer_y - round(27 * scale)),
              fill="#405276", width=max(1, round(scale)))
    draw.text((margin, footer_y), FOOTER,
              font=fit_text(draw, FOOTER, w - 2 * margin, round(13 * scale)), fill=MUTED, anchor="ls")
    output.parent.mkdir(parents=True, exist_ok=True)
    canvas.convert("RGB").save(output, optimize=True)


def main() -> None:
    pin = json.loads(PIN.read_text())
    assert sha256(SOLID) == pin["canonical_sha256"]["solid/r44_solid.json"]
    for path in (TILE, PARENT8, LEVEL64):
        assert path.exists()
    outputs = [
        ((1080, 1350), OUT / "why_translation_period_fails_portrait_1080x1350.png"),
        ((1080, 1080), OUT / "why_translation_period_fails_square_1080x1080.png"),
    ]
    for size, path in outputs:
        build(size, path)
    receipt = {
        "asset": "I08 — Why a translation period fails",
        "source_commit": pin["source_commit"],
        "canonical_solid_sha256": sha256(SOLID),
        "render_sources": {str(path.relative_to(ROOT)): sha256(path)
                           for path in (TILE, PARENT8, LEVEL64)},
        "diagram_scope": "Finite exact patches illustrate the hierarchy; the period descent is the theorem argument.",
        "outputs": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size,
                                                    "sha256": sha256(path)}
                    for _, path in outputs},
    }
    (OUT / "period_argument_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
