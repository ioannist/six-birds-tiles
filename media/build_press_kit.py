#!/usr/bin/env python3
"""Build I12: Chair44 press and presentation kit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps, PngImagePlugin
import qrcode

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / "output" / "press"
RAW_EXACT = HERE / "source" / "press_exact_raw"
RAW_MAP = HERE / "source" / "numbered_views_raw"
TILE = HERE / "source" / "feature_map" / "000090.png"
SOLID = ROOT / "solid" / "r44_solid.json"
PIN = ROOT / "reader" / "pin.json"

NAVY = "#1b2540"
NAVY2 = "#26325a"
CREAM = "#f4ecdf"
MUTED = "#c9cfe0"
GOLD = "#f3b53a"
CORAL = "#e8563f"
SKY = "#5aa9e6"
FONT_DIR = Path("/usr/share/fonts/truetype/dejavu")
FOOTER = "Ioannis Tsiokos · with ChatGPT Astra + Six Birds Theory · EmergenceCalculus.com/r44"
REPO_URL = "https://github.com/ioannist/six-birds-tiles#check-it-for-yourself"
VIEWS = [("px", "+X"), ("nx", "−X"), ("py", "+Y"),
         ("ny", "−Y"), ("pz", "+Z"), ("nz", "−Z")]


def sha256(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def font(size: int, bold: bool = False, serif: bool = False):
    family = "DejaVuSerif" if serif else "DejaVuSans"
    suffix = "-Bold.ttf" if bold else ".ttf"
    return ImageFont.truetype(str(FONT_DIR / (family + suffix)), max(7, size))


def fit_text(draw: ImageDraw.ImageDraw, copy: str, width: int, start: int,
             bold: bool = False, serif: bool = False, minimum: int = 8):
    size = start
    while size > minimum and draw.textlength(copy, font=font(size, bold, serif)) > width:
        size -= 1
    return font(size, bold, serif)


def wrapped_lines(draw: ImageDraw.ImageDraw, copy: str, face, width: int) -> list[str]:
    out, line = [], ""
    for word in copy.split():
        trial = f"{line} {word}".strip()
        if line and draw.textlength(trial, font=face) > width:
            out.append(line)
            line = word
        else:
            line = trial
    if line:
        out.append(line)
    return out


def draw_wrapped(draw, xy, copy, face, fill, width, spacing=None):
    rows = wrapped_lines(draw, copy, face, width)
    spacing = spacing if spacing is not None else max(4, face.size // 4)
    draw.multiline_text(xy, "\n".join(rows), font=face, fill=fill, spacing=spacing)
    return len(rows) * (face.size + spacing)


def field(size: tuple[int, int]) -> Image.Image:
    w, h = size
    top = Image.new("RGB", size, NAVY)
    bottom = Image.new("RGB", size, NAVY2)
    gradient = Image.linear_gradient("L").resize(size)
    canvas = Image.composite(bottom, top, gradient).convert("RGBA")
    glow = Image.new("RGBA", size, (0, 0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse((int(w * .42), -int(h * .28), int(w * 1.12), int(h * .88)),
               fill=(90, 169, 230, 22))
    return Image.alpha_composite(canvas, glow.filter(ImageFilter.GaussianBlur(max(30, w // 10))))


def crop_alpha(path: Path, pad: int = 24) -> Image.Image:
    image = Image.open(path).convert("RGBA")
    box = image.getchannel("A").getbbox()
    assert box
    box = (max(0, box[0] - pad), max(0, box[1] - pad),
           min(image.width, box[2] + pad), min(image.height, box[3] + pad))
    return image.crop(box)


def tile_image() -> Image.Image:
    return crop_alpha(TILE, 4)


def place(canvas: Image.Image, item: Image.Image, box: tuple[int, int, int, int], shadow=True):
    x0, y0, x1, y1 = box
    target = ImageOps.contain(item, (x1 - x0, y1 - y0), Image.Resampling.LANCZOS)
    x = x0 + (x1 - x0 - target.width) // 2
    y = y0 + (y1 - y0 - target.height) // 2
    if shadow:
        alpha = target.getchannel("A").filter(ImageFilter.GaussianBlur(max(4, target.width // 40)))
        shade = Image.new("RGBA", target.size, (2, 7, 18, 0))
        shade.putalpha(alpha.point(lambda value: value * 90 // 255))
        canvas.alpha_composite(shade, (x + target.width // 36, y + target.height // 30))
    canvas.alpha_composite(target, (x, y))


def footer(draw: ImageDraw.ImageDraw, w: int, h: int, margin: int, size: int) -> None:
    y = h - margin
    draw.line((margin, y - size * 1.7, w - margin, y - size * 1.7),
              fill="#405276", width=max(1, w // 1500))
    draw.text((margin, y), FOOTER,
              font=fit_text(draw, FOOTER, w - 2 * margin, size), fill=MUTED, anchor="ls")


def qr_image(size: int) -> Image.Image:
    qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M,
                       box_size=8, border=3)
    qr.add_data(REPO_URL)
    qr.make(fit=True)
    return qr.make_image(fill_color=NAVY, back_color=CREAM).convert("RGB").resize(
        (size, size), Image.Resampling.NEAREST).convert("RGBA")


def export_transparent_views(pin: dict) -> list[Path]:
    target = OUT / "transparent"
    target.mkdir(parents=True, exist_ok=True)
    outputs = []
    meta = PngImagePlugin.PngInfo()
    meta.add_text("Title", "Chair44 (R44) exact orthographic view")
    meta.add_text("Author", "Ioannis Tsiokos")
    meta.add_text("Credit", FOOTER)
    meta.add_text("SourceCommit", pin["source_commit"])
    meta.add_text("CanonicalSolidSHA256", sha256(SOLID))
    for directory, label in VIEWS:
        exact = crop_alpha(RAW_EXACT / directory / "000090.png", 30)
        annotated = crop_alpha(RAW_MAP / directory / "000090.png", 30)
        exact_path = target / f"chair44_exact_view_from_{directory}_transparent.png"
        map_path = target / f"chair44_feature_map_view_from_{directory}_transparent.png"
        exact.save(exact_path, pnginfo=meta, optimize=True)
        annotated.save(map_path, pnginfo=meta, optimize=True)
        outputs.extend((exact_path, map_path))
    return outputs


def copyspace(output: Path, tile_side: str) -> None:
    w, h = 2400, 1350
    canvas = field((w, h))
    draw = ImageDraw.Draw(canvas)
    margin = 86
    if tile_side == "right":
        tile_box = (1180, 115, 2290, 1080)
        label_x, anchor = 2260, "ra"
    else:
        tile_box = (110, 115, 1220, 1080)
        label_x, anchor = 140, "la"
    place(canvas, tile_image(), tile_box)
    draw.rounded_rectangle((label_x - 390 if tile_side == "right" else label_x,
                            1040,
                            label_x if tile_side == "right" else label_x + 390,
                            1112), radius=16, fill=CREAM, outline=GOLD, width=3)
    draw.text((label_x - 195 if tile_side == "right" else label_x + 195, 1076),
              "EXACT SOLID · FEATURE MAP ANNOTATION",
              font=fit_text(draw, "EXACT SOLID · FEATURE MAP ANNOTATION", 350, 18, True),
              fill=NAVY, anchor="mm")
    footer(draw, w, h, margin, 19)
    output.parent.mkdir(parents=True, exist_ok=True)
    canvas.convert("RGB").save(output, optimize=True)


def title_slide(output: Path) -> None:
    w, h = 1920, 1080
    canvas = field((w, h))
    draw = ImageDraw.Draw(canvas)
    margin = 90
    draw.text((margin, 100), "Chair44", font=font(94, True, True), fill=CREAM)
    lead = draw.textlength("Chair44 ", font=font(94, True, True))
    draw.text((margin + lead, 100), "(R44)", font=font(94, True, True), fill=GOLD)
    draw.text((margin, 235), "A STRONGLY APERIODIC MONOTILE IN THREE DIMENSIONS",
              font=fit_text(draw, "A STRONGLY APERIODIC MONOTILE IN THREE DIMENSIONS",
                            910, 30, True), fill=MUTED)
    draw.text((margin, 365), "One shape.", font=font(52, True), fill=CREAM)
    draw.text((margin, 438), "It tiles space.", font=font(52, True), fill=CREAM)
    draw.text((margin, 511), "No tiling has a translation period.",
              font=fit_text(draw, "No tiling has a translation period.", 900, 52, True), fill=CREAM)
    draw.text((margin, 655), "Proof submission · exact rational solid and reproducible evidence",
              font=fit_text(draw, "Proof submission · exact rational solid and reproducible evidence",
                            900, 26), fill=SKY)
    place(canvas, tile_image(), (1000, 100, 1820, 850))
    draw.rounded_rectangle((1170, 800, 1740, 870), radius=15, fill=CREAM, outline=GOLD, width=2)
    draw.text((1455, 835), "FEATURE COLOURS ARE ANNOTATIONS",
              font=font(18, True), fill=NAVY, anchor="mm")
    footer(draw, w, h, margin, 17)
    canvas.convert("RGB").save(output, optimize=True)


def theorem_slide(output: Path) -> None:
    w, h = 1920, 1080
    canvas = field((w, h))
    draw = ImageDraw.Draw(canvas)
    margin = 90
    draw.text((margin, 92), "THE THEOREM", font=font(31, True), fill=GOLD)
    draw.text((margin, 150), "Chair44 (R44)", font=font(64, True, True), fill=CREAM)
    theorem = ("The explicit rational polyhedral 3-ball Q tiles Euclidean 3-space by congruent "
               "copies, and every such tiling has no nonzero translation period and a symmetry "
               "group of order at most 24.")
    face = font(35, True, True)
    draw_wrapped(draw, (margin, 280), theorem, face, CREAM, 1030, 16)
    facts = [("EXISTENCE", "tiles space"), ("TRANSLATIONS", "only the zero period"),
             ("FULL SYMMETRY", "finite · order at most 24")]
    y = 605
    for heading, value in facts:
        draw.rounded_rectangle((margin, y, 1080, y + 76), radius=14,
                               fill=CREAM, outline=GOLD, width=2)
        draw.text((margin + 24, y + 38), heading, font=font(18, True), fill=CORAL, anchor="lm")
        draw.text((margin + 310, y + 38), value, font=font(22, True), fill=NAVY, anchor="lm")
        y += 92
    place(canvas, tile_image(), (1160, 145, 1840, 845))
    draw.text((1500, 890), "Exact solid · feature map annotation", font=font(17), fill=SKY, anchor="ma")
    footer(draw, w, h, margin, 17)
    canvas.convert("RGB").save(output, optimize=True)


def a4_press(output: Path) -> None:
    w, h = 2480, 3508
    canvas = field((w, h))
    draw = ImageDraw.Draw(canvas)
    margin = 150
    draw.text((margin, 145), "Chair44", font=font(150, True, True), fill=CREAM)
    lead = draw.textlength("Chair44 ", font=font(150, True, True))
    draw.text((margin + lead, 145), "(R44)", font=font(150, True, True), fill=GOLD)
    draw.text((margin, 335), "A THREE-DIMENSIONAL APERIODIC MONOTILE",
              font=fit_text(draw, "A THREE-DIMENSIONAL APERIODIC MONOTILE",
                            w - 2 * margin, 52, True), fill=MUTED)
    place(canvas, tile_image(), (260, 465, 2220, 1970))
    draw.rounded_rectangle((555, 1885, 1925, 1990), radius=22,
                           fill=CREAM, outline=GOLD, width=4)
    draw.text((1240, 1938), "EXACT SOLID · FEATURE MAP ANNOTATION",
              font=font(31, True), fill=NAVY, anchor="mm")
    claim = "One shape tiles space, yet no tiling by it has a nonzero translation period."
    draw_wrapped(draw, (margin, 2100), claim, font(66, True, True), CREAM,
                 w - 2 * margin, 22)
    cards = [
        ("IT TILES SPACE", "A nested exact construction supplies tilings of all Euclidean space."),
        ("EVERY TILING IS CONTROLLED", "The solid's geometry forces registration and a unique parent hierarchy."),
        ("NO PERIOD SURVIVES", "Coarsening sends a period p to p/2 repeatedly; only p = 0 remains integral."),
    ]
    y = 2465
    for heading, detail in cards:
        draw.rounded_rectangle((margin, y, w - margin, y + 205), radius=24,
                               fill=CREAM, outline=GOLD, width=3)
        draw.text((margin + 42, y + 43), heading, font=font(32, True), fill=CORAL)
        draw.text((margin + 42, y + 102), detail,
                  font=fit_text(draw, detail, w - 2 * margin - 84, 30), fill=NAVY)
        y += 235
    qr = qr_image(245)
    canvas.alpha_composite(qr, (w - margin - 245, 3150))
    draw.text((margin, 3195), "EXPLORE THE TILE · RUN THE CHECKS · READ THE PROOF",
              font=fit_text(draw, "EXPLORE THE TILE · RUN THE CHECKS · READ THE PROOF",
                            1720, 31, True), fill=GOLD)
    draw.text((margin, 3265), "github.com/ioannist/six-birds-tiles",
              font=font(36, True), fill=CREAM)
    footer(draw, w, h, margin, 25)
    canvas.convert("RGB").save(output, dpi=(300, 300), optimize=True)


def write_copy(path: Path, pin: dict) -> None:
    path.write_text(f"""# Chair44 (R44) press copy

## Caption

Chair44 (R44) is one connected, unmarked three-dimensional solid that tiles
Euclidean space, while every tiling by congruent copies has no nonzero
translation period. The coral and sky markings in explanatory images identify
geometric bumps and dents; they are annotations, not colours on the tile.

## Short description

Chair44 is an explicit rational polyhedral 3-ball built on the seven-cube chair.
Its 192 tiny complementary features restrict how copies meet. The submitted
proof establishes existence, registration of arbitrary tilings, a unique
self-preserving parent hierarchy, and repeated period halving.

## Long description

Chair44 (formally R44) is a proposed strongly aperiodic monotile for three-
dimensional Euclidean space. It admits tilings by congruent copies, including
reflections, but no such tiling has a nonzero translation period; its full
symmetry group has order at most 24. The exact solid, paper, finite certificate
replay, Lean sources, executable notebook, browser viewer, and an AI review
package are available in the repository so readers can inspect the claim at
their preferred technical level.

## Credit line

{FOOTER}

## Short alt text

Chair44, a white three-dimensional chair-shaped solid with annotated geometric
bumps in coral and dents outlined in sky blue.

## Medium alt text

An isometric view of Chair44 (R44), shaped like a two-by-two-by-two block with
one corner missing. Its exposed square panels carry rings of tiny complementary
pyramidal bumps and dents, enlarged and coloured only for visibility.

## Long alt text

The image shows Chair44 (R44), an exact rational polyhedral solid based on seven
unit cubes arranged as a two-by-two-by-two block with the upper front corner
removed. Each of its 24 exposed unit-square panels carries eight very small
square-pyramidal features. Filled coral squares mark outward bumps and hollow
sky-blue squares mark inward dents; these marks are a display overlay and the
mathematical tile is one unmarked solid. Accompanying text states that Chair44
tiles three-dimensional space and that no tiling by it has a nonzero
translation period.

## Source identity

- Repository snapshot: `{pin['source_commit']}`
- Canonical JSON SHA-256: `{sha256(SOLID)}`
- Project page: `https://www.EmergenceCalculus.com/r44`
- Repository: `https://github.com/ioannist/six-birds-tiles`
""")


def contact_sheet(paths: list[Path], transparent: list[Path], output: Path) -> None:
    canvas = Image.new("RGB", (2400, 2400), NAVY)
    draw = ImageDraw.Draw(canvas)
    # Copy-space pair and presentation pair.
    boxes = [(20, 20, 1180, 670), (1220, 20, 2380, 670),
             (20, 700, 1180, 1350), (1220, 700, 2380, 1350)]
    for path, box in zip(paths[:4], boxes):
        thumb = ImageOps.contain(Image.open(path).convert("RGB"),
                                 (box[2] - box[0], box[3] - box[1]), Image.Resampling.LANCZOS)
        x = box[0] + (box[2] - box[0] - thumb.width) // 2
        y = box[1] + (box[3] - box[1] - thumb.height) // 2
        canvas.paste(thumb, (x, y))
    # A4 image at left; six annotated and six exact directions at right.
    a4_box = (20, 1380, 690, 2300)
    a4 = ImageOps.contain(Image.open(paths[4]).convert("RGB"),
                          (a4_box[2] - a4_box[0], a4_box[3] - a4_box[1]), Image.Resampling.LANCZOS)
    canvas.paste(a4, (a4_box[0] + (a4_box[2] - a4_box[0] - a4.width) // 2,
                      a4_box[1] + (a4_box[3] - a4_box[1] - a4.height) // 2))
    exacts = [p for p in transparent if "_exact_" in p.name]
    maps = [p for p in transparent if "_feature_map_" in p.name]
    draw.text((735, 1415), "SIX TRANSPARENT DIRECTIONS", font=font(27, True), fill=GOLD)
    draw.text((735, 1455), "top two rows: true geometry · bottom two rows: feature-map annotation",
              font=font(16), fill=MUTED)
    for row, group in enumerate((exacts, maps)):
        for i, path in enumerate(group):
            x = 735 + (i % 3) * 545
            y = 1490 + row * 400 + (i // 3) * 195
            card_fill = "#344367" if row == 0 else CREAM
            draw.rounded_rectangle((x, y, x + 510, y + 170), radius=12,
                                   fill=card_fill, outline=GOLD, width=2)
            image = ImageOps.contain(Image.open(path).convert("RGBA"), (440, 145), Image.Resampling.LANCZOS)
            canvas.paste(image.convert("RGB"), (x + (510 - image.width) // 2,
                                                 y + (170 - image.height) // 2), image)
    draw.text((20, 2360), "PRESS AND PRESENTATION KIT · REVIEW CONTACT SHEET",
              font=font(23, True), fill=CREAM)
    output.parent.mkdir(parents=True, exist_ok=True)
    canvas.save(output, optimize=True)


def main() -> None:
    pin = json.loads(PIN.read_text())
    assert sha256(SOLID) == pin["canonical_sha256"]["solid/r44_solid.json"]
    OUT.mkdir(parents=True, exist_ok=True)
    transparent = export_transparent_views(pin)
    composed = [OUT / "hero_copy_space_left_2400x1350.png",
                OUT / "hero_copy_space_right_2400x1350.png",
                OUT / "title_slide_1920x1080.png",
                OUT / "theorem_slide_1920x1080.png",
                OUT / "chair44_press_a4_2480x3508.png"]
    copyspace(composed[0], "right")
    copyspace(composed[1], "left")
    title_slide(composed[2])
    theorem_slide(composed[3])
    a4_press(composed[4])
    copy_path = OUT / "PRESS_COPY.md"
    write_copy(copy_path, pin)
    contact = OUT / "press_kit_contact_sheet_2400x2400.png"
    contact_sheet(composed, transparent, contact)
    all_outputs = transparent + composed + [copy_path, contact]
    receipt = {
        "asset": "I12 — press and presentation kit",
        "source_commit": pin["source_commit"],
        "canonical_solid_sha256": sha256(SOLID),
        "transparent_views": {"true_geometry": 6, "feature_map_annotation": 6,
                              "credit": "Embedded in PNG metadata; visible credit is retained on composed assets."},
        "outputs": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size,
                                                    "sha256": sha256(path)} for path in all_outputs},
    }
    (OUT / "press_kit_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
