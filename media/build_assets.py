#!/usr/bin/env python3
"""Build deterministic Chair44 campaign images around exact rendered geometry."""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / "output"
BACKGROUND = HERE / "backgrounds" / "editorial_navy_v1.png"
TILE = HERE / "source" / "feature_map" / "000090.png"
EXACT_TILE = HERE / "source" / "000090.png"
PLAIN_TILE = HERE / "source" / "plain" / "000810.png"
PERIODIC_VIEW = ROOT / "video" / "output" / "final" / "frames" / "001440.png"
GROWTH_64 = ROOT / "video" / "output" / "final" / "frames" / "003810.png"
GROWTH_4096 = ROOT / "video" / "output" / "final" / "frames" / "004140.png"
ASSEMBLY_8 = ROOT / "video" / "output" / "final" / "frames" / "003600.png"
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


def sha256(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def font(size: int, bold: bool = False, serif: bool = False) -> ImageFont.FreeTypeFont:
    family = "DejaVuSerif" if serif else "DejaVuSans"
    suffix = "-Bold.ttf" if bold else ".ttf"
    return ImageFont.truetype(str(FONT_DIR / (family + suffix)), max(6, size))


def fit_text(draw: ImageDraw.ImageDraw, copy: str, max_width: int, start: int,
             *, bold: bool = False, serif: bool = False, minimum: int = 8):
    size = start
    while size > minimum and draw.textlength(copy, font=font(size, bold, serif)) > max_width:
        size -= 1
    return font(size, bold, serif)


def wrapped_lines(draw: ImageDraw.ImageDraw, copy: str, face: ImageFont.FreeTypeFont,
                  max_width: int) -> list[str]:
    words = copy.split()
    lines: list[str] = []
    line = ""
    for word in words:
        trial = f"{line} {word}".strip()
        if line and draw.textlength(trial, font=face) > max_width:
            lines.append(line)
            line = word
        else:
            line = trial
    if line:
        lines.append(line)
    return lines


def draw_wrapped(draw: ImageDraw.ImageDraw, xy: tuple[int, int], copy: str,
                 face: ImageFont.FreeTypeFont, fill: str, max_width: int,
                 spacing: int | None = None) -> int:
    lines = wrapped_lines(draw, copy, face, max_width)
    spacing = spacing or max(4, face.size // 4)
    draw.multiline_text(xy, "\n".join(lines), font=face, fill=fill, spacing=spacing)
    return len(lines) * (face.size + spacing)


def cover(image: Image.Image, size: tuple[int, int]) -> Image.Image:
    return ImageOps.fit(image, size, method=Image.Resampling.LANCZOS,
                        centering=(0.5, 0.5)).convert("RGBA")


def exact_panel_features() -> list[tuple[int, float, float]]:
    """Return face 13's exact signs and tangent coordinates from canonical JSON."""
    solid = json.loads(SOLID.read_text())
    records = []
    for patch in solid["patches"]:
        if patch["face"] != 13:
            continue
        centre = [sum((Fraction(v) for v in axis), Fraction()) / 4
                  for axis in zip(*patch["base"])]
        records.append((int(patch["coefficient"]), float(centre[0] % 1),
                        float(centre[2] % 1)))
    assert len(records) == 8
    assert {abs(value) for value, _, _ in records} == {9, 10, 11, 12}
    return records


FEATURES = exact_panel_features()


def add_tile(canvas: Image.Image, box: tuple[int, int, int, int], source: Path = TILE) -> None:
    tile = Image.open(source).convert("RGBA")
    alpha_box = tile.getchannel("A").getbbox()
    assert alpha_box
    tile = tile.crop(alpha_box)
    x0, y0, x1, y1 = box
    target = ImageOps.contain(tile, (x1 - x0, y1 - y0), Image.Resampling.LANCZOS)
    px = x0 + (x1 - x0 - target.width) // 2
    py = y0 + (y1 - y0 - target.height) // 2
    shadow_alpha = target.getchannel("A").filter(ImageFilter.GaussianBlur(max(4, target.width // 45)))
    shadow = Image.new("RGBA", target.size, (4, 12, 25, 0))
    shadow.putalpha(shadow_alpha.point(lambda value: value * 90 // 255))
    canvas.alpha_composite(shadow, (px + target.width // 35, py + target.height // 28))
    canvas.alpha_composite(target, (px, py))


def feature_card(canvas: Image.Image, box: tuple[int, int, int, int], horizontal: bool) -> None:
    d = ImageDraw.Draw(canvas)
    x0, y0, x1, y1 = box
    width, height = x1 - x0, y1 - y0
    radius = max(5, min(width, height) // 18)
    d.rounded_rectangle(box, radius=radius, fill=CREAM, outline=GOLD,
                        width=max(2, width // 180))
    pad = max(10, width // 24)
    title_size = max(9, min(21, width // 18))
    d.text((x0 + pad, y0 + pad), "FEATURE MAP · ANNOTATION",
           font=fit_text(d, "FEATURE MAP · ANNOTATION", width - 2 * pad,
                         title_size, bold=True), fill=NAVY)
    if horizontal:
        map_box = (x0 + pad, y0 + height * .34, x0 + width * .48, y1 - pad)
        legend_x = x0 + width * .54
        legend_y = y0 + height * .42
    else:
        map_box = (x0 + pad, y0 + height * .22, x1 - pad, y0 + height * .72)
        legend_x = x0 + pad
        legend_y = y0 + height * .79
    mx0, my0, mx1, my1 = map_box
    side = min(mx1 - mx0, my1 - my0)
    ox, oy = (mx0 + mx1 - side) / 2, (my0 + my1 - side) / 2
    marker = max(3, int(side * .055))
    line = max(2, marker // 3)
    for value, u, v in FEATURES:
        x, y = ox + u * side, oy + v * side
        if value > 0:
            d.rectangle((x - marker, y - marker, x + marker, y + marker), fill=CORAL)
        else:
            d.rectangle((x - marker, y - marker, x + marker, y + marker),
                        fill=CREAM, outline=SKY, width=line)
    legend_size = max(8, min(17, width // 24))
    icon = max(4, legend_size // 2)
    base_y = legend_y + legend_size // 2
    d.rectangle((legend_x, base_y - icon, legend_x + 2 * icon, base_y + icon), fill=CORAL)
    d.text((legend_x + 3 * icon, legend_y), "bump", font=font(legend_size), fill=NAVY)
    second_x = legend_x + max(72, width * .19)
    d.rectangle((second_x, base_y - icon, second_x + 2 * icon, base_y + icon),
                fill=CREAM, outline=SKY, width=max(2, icon // 3))
    d.text((second_x + 3 * icon, legend_y), "dent", font=font(legend_size), fill=NAVY)
    d.text((legend_x, legend_y + legend_size * 1.45),
           "Colour and symbols are annotations.", font=font(legend_size), fill=NAVY)


def overlay_legend(canvas: Image.Image, box: tuple[int, int, int, int]) -> None:
    d = ImageDraw.Draw(canvas)
    x0, y0, x1, y1 = box
    width, height = x1 - x0, y1 - y0
    radius = max(5, height // 7)
    d.rounded_rectangle(box, radius=radius, fill=CREAM, outline=GOLD,
                        width=max(2, width // 350))
    pad = max(10, width // 28)
    title_size = max(9, min(20, height // 4))
    title = "FEATURE OVERLAY · ANNOTATION"
    d.text((x0 + pad, y0 + pad), title,
           font=fit_text(d, title, width * .48, title_size, bold=True), fill=NAVY)
    label_size = max(8, min(17, height // 5))
    icon = max(4, label_size // 2)
    ly = y0 + pad
    first_x = x0 + width * .56
    d.rectangle((first_x, ly + 2, first_x + icon * 2, ly + icon * 2 + 2), fill=CORAL)
    d.text((first_x + icon * 3, ly), "bump", font=font(label_size), fill=NAVY)
    second_x = x0 + width * .74
    d.rectangle((second_x, ly + 2, second_x + icon * 2, ly + icon * 2 + 2),
                fill=CREAM, outline=SKY, width=max(2, icon // 3))
    d.text((second_x + icon * 3, ly), "dent", font=font(label_size), fill=NAVY)
    note = "Colours and symbols identify geometric bumps and dents."
    d.text((x0 + pad, y1 - pad), note,
           font=fit_text(d, note, width - 2 * pad, label_size), fill=NAVY, anchor="ls")


def background(size: tuple[int, int]) -> Image.Image:
    im = cover(Image.open(BACKGROUND), size)
    shade = Image.new("RGBA", size, (27, 37, 64, 70))
    return Image.alpha_composite(im, shade)


def simple_background(size: tuple[int, int]) -> Image.Image:
    """Quiet campaign field for wide crops; no decorative geometry near copy."""
    width, height = size
    top = Image.new("RGB", size, NAVY)
    bottom = Image.new("RGB", size, NAVY2)
    gradient = Image.linear_gradient("L").resize(size)
    im = Image.composite(bottom, top, gradient).convert("RGBA")
    glow = Image.new("RGBA", size, (0, 0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse((int(width * .43), -int(height * .3), int(width * 1.05), int(height * 1.15)),
               fill=(90, 169, 230, 24))
    glow = glow.filter(ImageFilter.GaussianBlur(max(30, width // 12)))
    return Image.alpha_composite(im, glow)


def footer(draw: ImageDraw.ImageDraw, width: int, height: int, margin: int) -> None:
    size = max(7, min(20, width // 72))
    f = fit_text(draw, FOOTER, width - 2 * margin, size)
    y = height - margin
    draw.line((margin, y - size * 1.2, width - margin, y - size * 1.2),
              fill=(201, 207, 224, 100), width=max(1, width // 1100))
    draw.text((margin, y), FOOTER, font=f, fill=MUTED, anchor="ls")


def hero(size: tuple[int, int], output: Path) -> None:
    width, height = size
    margin = max(18, int(min(width, height) * .065))
    landscape = width / height >= 1.45
    im = simple_background(size) if landscape else background(size)
    d = ImageDraw.Draw(im)
    if landscape:
        wordmark_size = int(height * .068)
        wordmark_x = margin
        d.text((wordmark_x, margin), "Chair44 ", font=font(wordmark_size, True, True), fill=CREAM)
        lead = d.textlength("Chair44 ", font=font(wordmark_size, True, True))
        d.text((wordmark_x + lead, margin), "(R44)", font=font(wordmark_size, True, True), fill=GOLD)
        claim_size = int(height * .069)
        claim_y = margin + wordmark_size * 1.75
        lines = ["One shape.", "It tiles space.", "No tiling has a", "translation period."]
        for i, line in enumerate(lines):
            d.text((margin, claim_y + i * claim_size * 1.16), line,
                   font=font(claim_size, i in (0, 3)), fill=CREAM)
        d.text((margin, int(height * .73)), "A three-dimensional aperiodic monotile",
               font=font(int(height * .031)), fill=MUTED)
        tag_width = int(width * .22)
        d.rounded_rectangle((margin, int(height * .80), margin + tag_width, int(height * .85)),
                            radius=max(4, height // 90), fill=NAVY2, outline=GOLD,
                            width=max(1, width // 900))
        tag = "EXACT SOLID · ANNOTATED"
        d.text((margin + tag_width / 2, int(height * .825)), tag,
               font=fit_text(d, tag, tag_width - 18, int(height * .018), bold=True),
               fill=GOLD, anchor="mm")
        add_tile(im, (int(width * .46), int(height * .10), int(width * .94), int(height * .68)))
        overlay_legend(im, (int(width * .55), int(height * .75), int(width * .94), int(height * .88)))
    else:
        wordmark_size = int(width * .075)
        d.text((margin, margin), "Chair44 ", font=font(wordmark_size, True, True), fill=CREAM)
        lead = d.textlength("Chair44 ", font=font(wordmark_size, True, True))
        d.text((margin + lead, margin), "(R44)", font=font(wordmark_size, True, True), fill=GOLD)
        claim_y = margin + wordmark_size * 1.55
        claim_size = int(width * .045)
        d.text((margin, claim_y),
               "One shape. It tiles space.\nNo tiling has a translation period.",
               font=font(claim_size, True), fill=CREAM,
               spacing=int(width * .016))
        tile_top = max(int(height * .19), int(claim_y + claim_size * 2.15))
        if height / width > 1.5:
            tile_box = (int(width * .20), tile_top, int(width * .80), int(height * .58))
        else:
            tile_top = max(tile_top, int(height * .33))
            tile_box = (int(width * .19), tile_top, int(width * .81), int(height * .59))
        add_tile(im, tile_box)
        overlay_legend(im, (margin, int(height * .68), width - margin, int(height * .79)))
        d.text((margin, int(height * .875)), "A three-dimensional aperiodic monotile · exact solid with feature overlay",
               font=fit_text(d, "A three-dimensional aperiodic monotile · exact solid with feature overlay",
                             width - 2 * margin, int(width * .026)), fill=MUTED)
    footer(d, width, height, margin)
    output.parent.mkdir(parents=True, exist_ok=True)
    im.convert("RGB").save(output, optimize=True)


def review_320(source: Path, output: Path) -> None:
    # Native small-format review: retain the feature ribbon but simplify prose.
    width = height = 320
    im = background((width, height))
    d = ImageDraw.Draw(im)
    d.text((18, 15), "Chair44 ", font=font(23, True, True), fill=CREAM)
    lead = d.textlength("Chair44 ", font=font(23, True, True))
    d.text((18 + lead, 15), "(R44)", font=font(23, True, True), fill=GOLD)
    add_tile(im, (105, 44, 310, 197))
    overlay_legend(im, (18, 205, 302, 275))
    footer(d, width, height, 18)
    im.convert("RGB").save(output, optimize=True)


def rounded_image(canvas: Image.Image, source: Path, box: tuple[int, int, int, int], radius: int) -> None:
    x0, y0, x1, y1 = box
    art = ImageOps.fit(Image.open(source).convert("RGB"), (x1 - x0, y1 - y0),
                       method=Image.Resampling.LANCZOS, centering=(.5, .5)).convert("RGBA")
    mask = Image.new("L", art.size)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, art.width - 1, art.height - 1), radius=radius, fill=255)
    art.putalpha(mask)
    canvas.alpha_composite(art, (x0, y0))


def comparison(size: tuple[int, int], output: Path) -> None:
    width, height = size
    im = simple_background(size)
    d = ImageDraw.Draw(im)
    margin = max(28, int(min(width, height) * .055))
    title_size = int(min(width, height) * .064)
    d.text((margin, margin), "Almost the same chair.", font=font(title_size, True, True), fill=CREAM)
    d.text((margin, margin + title_size * 1.3),
           "One admits a repeating tiling. Chair44 admits none with a translation period.",
           font=fit_text(d, "One admits a repeating tiling. Chair44 admits none with a translation period.",
                         width - 2 * margin, int(title_size * .48)), fill=MUTED)
    landscape = width / height > 1.3
    if landscape:
        gap = int(width * .035)
        card_top, card_bottom = int(height * .22), int(height * .89)
        card_width = (width - 2 * margin - gap) // 2
        boxes = [(margin, card_top, margin + card_width, card_bottom),
                 (margin + card_width + gap, card_top, width - margin, card_bottom)]
        for box in boxes:
            d.rounded_rectangle(box, radius=16, fill="#202d4d", outline="#405276", width=2)
        lx0, ly0, lx1, ly1 = boxes[0]
        rx0, ry0, rx1, ry1 = boxes[1]
        d.text((lx0 + 32, ly0 + 28), "PLAIN CHAIR · PERIODIC CONTROL", font=font(22, True), fill=GOLD)
        d.text((rx0 + 32, ry0 + 28), "CHAIR44 (R44)", font=font(22, True), fill=GOLD)
        tile_y0, tile_y1 = ly0 + 75, ly0 + int((ly1 - ly0) * .60)
        add_tile(im, (lx0 + 65, tile_y0, lx1 - 65, tile_y1), PLAIN_TILE)
        add_tile(im, (rx0 + 65, tile_y0, rx1 - 65, tile_y1), TILE)
        inset = (lx0 + 35, ly0 + int((ly1 - ly0) * .62), lx1 - 35, ly1 - 62)
        rounded_image(im, PERIODIC_VIEW, inset, 10)
        d.rounded_rectangle((inset[0] + 12, inset[1] + 12, inset[0] + 330, inset[1] + 50),
                            radius=8, fill=(27, 37, 64, 225))
        d.text((inset[0] + 25, inset[1] + 29), "FINITE VIEW OF A PERIODIC TILING",
               font=font(16, True), fill=CREAM, anchor="lm")
        d.text((rx0 + 45, ry0 + int((ry1 - ry0) * .67)),
               "Filled coral: bump   ·   Hollow sky: dent", font=font(19), fill=CREAM)
        d.text((rx0 + 45, ry0 + int((ry1 - ry0) * .75)),
               "The feature overlay is annotation.\nThe geometry itself restricts which copies can meet.",
               font=font(22), fill=MUTED, spacing=10)
        d.text((rx0 + 45, ry0 + int((ry1 - ry0) * .88)),
               "EVERY TILING: NO NONZERO TRANSLATION PERIOD", font=font(20, True), fill=GOLD)
    else:
        card_left, card_right = margin, width - margin
        top1, bottom1 = int(height * .18), int(height * .53)
        top2, bottom2 = int(height * .55), int(height * .91)
        for box in [(card_left, top1, card_right, bottom1), (card_left, top2, card_right, bottom2)]:
            d.rounded_rectangle(box, radius=14, fill="#202d4d", outline="#405276", width=2)
        d.text((card_left + 25, top1 + 22), "PLAIN CHAIR · PERIODIC CONTROL", font=font(19, True), fill=GOLD)
        d.text((card_left + 25, top2 + 22), "CHAIR44 (R44)", font=font(19, True), fill=GOLD)
        tile_size = int(width * .38)
        add_tile(im, (card_left + 30, top1 + 55, card_left + 30 + tile_size, bottom1 - 28), PLAIN_TILE)
        add_tile(im, (card_left + 30, top2 + 55, card_left + 30 + tile_size, bottom2 - 35), TILE)
        inset = (card_left + int(width * .46), top1 + 70, card_right - 25, bottom1 - 48)
        rounded_image(im, PERIODIC_VIEW, inset, 8)
        d.text((inset[0], bottom1 - 38), "Finite view of a periodic tiling", font=font(14, True), fill=CREAM)
        text_x = card_left + int(width * .46)
        d.text((text_x, top2 + 90), "Filled coral: bump\nHollow sky: dent",
               font=font(17), fill=CREAM, spacing=8)
        d.text((text_x, top2 + 175), "Feature overlay:\nannotation over exact solid",
               font=font(16), fill=MUTED, spacing=8)
        d.text((text_x, top2 + 265), "No tiling has a\ntranslation period.",
               font=font(19, True), fill=GOLD, spacing=7)
    footer(d, width, height, margin)
    output.parent.mkdir(parents=True, exist_ok=True)
    im.convert("RGB").save(output, optimize=True)


def build_hero() -> dict:
    specs = {
        "hero_github_1280x640.png": (1280, 640),
        "hero_open_graph_1200x630.png": (1200, 630),
        "hero_landscape_1920x1080.png": (1920, 1080),
        "hero_square_1080x1080.png": (1080, 1080),
        "hero_portrait_1080x1350.png": (1080, 1350),
        "hero_story_1080x1920.png": (1080, 1920),
    }
    hero_dir = OUT / "hero"
    for name, size in specs.items():
        hero(size, hero_dir / name)
    review_320(hero_dir / "hero_square_1080x1080.png", hero_dir / "hero_square_320_review.png")
    outputs = sorted(hero_dir.glob("*.png"))
    return {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size, "sha256": sha256(path),
                                         "dimensions": list(Image.open(path).size)}
            for path in outputs}


def build_comparison() -> dict:
    specs = {
        "comparison_landscape_1920x1080.png": (1920, 1080),
        "comparison_portrait_1080x1350.png": (1080, 1350),
    }
    outdir = OUT / "comparison"
    for name, size in specs.items():
        comparison(size, outdir / name)
    outputs = sorted(outdir.glob("*.png"))
    receipt = {
        "asset_family": "I07 negative control",
        "source_commit": json.loads(PIN.read_text())["source_commit"],
        "plain_tile_sha256": sha256(PLAIN_TILE),
        "chair44_feature_overlay_sha256": sha256(TILE),
        "periodic_finite_view_sha256": sha256(PERIODIC_VIEW),
        "periodic_basis": json.loads((ROOT / "video" / ".cache" / "scene_data.json").read_text())["periodic_basis"],
        "footer": FOOTER,
        "outputs": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size,
                                                   "sha256": sha256(path),
                                                   "dimensions": list(Image.open(path).size)}
                    for path in outputs},
    }
    (OUT / "comparison_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def growth(size: tuple[int, int], output: Path) -> None:
    width, height = size
    im = simple_background(size)
    d = ImageDraw.Draw(im)
    margin = max(28, int(min(width, height) * .055))
    title_size = int(min(width, height) * .06)
    growth_title = "One tile. A hierarchy into space."
    title_face = fit_text(d, growth_title, width - 2 * margin, title_size,
                          bold=True, serif=True)
    d.text((margin, margin), growth_title, font=title_face, fill=CREAM)
    subtitle = "1 → 64 → 4,096 copies · finite exact placement views"
    d.text((margin, margin + title_size * 1.35), subtitle,
           font=fit_text(d, subtitle, width - 2 * margin, int(title_size * .48)), fill=MUTED)
    landscape = width / height > 1.3
    stages = [
        ("1", "Chair44", TILE, "Feature overlay · annotation"),
        ("64", "copies", GROWTH_64, "Features below display scale"),
        ("4,096", "copies", GROWTH_4096, "Features below display scale"),
    ]
    if landscape:
        gap = int(width * .025)
        top, bottom = int(height * .24), int(height * .77)
        card_width = (width - 2 * margin - 2 * gap) // 3
        for i, (count, unit, source, note) in enumerate(stages):
            x0 = margin + i * (card_width + gap)
            x1 = x0 + card_width
            d.rounded_rectangle((x0, top, x1, bottom), radius=16,
                                fill="#202d4d", outline="#405276", width=2)
            d.text((x0 + 26, top + 20), count, font=font(int(height * .058), True), fill=GOLD)
            count_width = d.textlength(count, font=font(int(height * .058), True))
            d.text((x0 + 36 + count_width, top + 45), unit.upper(),
                   font=font(int(height * .020), True), fill=CREAM, anchor="lm")
            art_box = (x0 + 22, top + int(height * .10), x1 - 22, bottom - int(height * .095))
            if i == 0:
                add_tile(im, art_box, source)
            else:
                rounded_image(im, source, art_box, 10)
            d.text((x0 + 26, bottom - int(height * .055)), "FINITE VIEW", font=font(17, True), fill=GOLD)
            d.text((x0 + 26, bottom - int(height * .025)), note,
                   font=fit_text(d, note, card_width - 52, 16), fill=MUTED)
            if i < 2:
                arrow_x = x1 + gap / 2
                d.line((arrow_x - 12, (top + bottom) / 2, arrow_x + 12, (top + bottom) / 2),
                       fill=GOLD, width=3)
                d.polygon(((arrow_x + 12, (top + bottom) / 2),
                           (arrow_x + 2, (top + bottom) / 2 - 7),
                           (arrow_x + 2, (top + bottom) / 2 + 7)), fill=GOLD)
        theorem = "The pictures establish finite compatible patches. The theorem excludes translation periods in every tiling."
        d.text((margin, int(height * .82)), theorem,
               font=fit_text(d, theorem, width - 2 * margin, int(height * .026)), fill=CREAM)
        d.text((margin, int(height * .87)), "Colours identify copies; Chair44 is one unmarked solid.",
               font=font(int(height * .020)), fill=MUTED)
    else:
        top = int(height * .19)
        card_height = int(height * .205)
        gap = int(height * .018)
        for i, (count, unit, source, note) in enumerate(stages):
            y0 = top + i * (card_height + gap)
            y1 = y0 + card_height
            d.rounded_rectangle((margin, y0, width - margin, y1), radius=14,
                                fill="#202d4d", outline="#405276", width=2)
            label_x = margin + 24
            d.text((label_x, y0 + 24), count, font=font(int(width * .052), True), fill=GOLD)
            d.text((label_x, y0 + int(width * .09)), unit.upper(), font=font(17, True), fill=CREAM)
            d.text((label_x, y1 - 45), "FINITE VIEW", font=font(14, True), fill=GOLD)
            d.text((label_x, y1 - 23), note,
                   font=fit_text(d, note, int(width * .39), 13), fill=MUTED)
            art_box = (int(width * .43), y0 + 12, width - margin - 15, y1 - 12)
            if i == 0:
                add_tile(im, art_box, source)
            else:
                rounded_image(im, source, art_box, 8)
        theorem = "Finite patches show that Chair44 tiles space.\nThe theorem rules out translation periods in every tiling."
        d.multiline_text((margin, int(height * .87)), theorem,
                         font=fit_text(d, theorem.splitlines()[1], width - 2 * margin,
                                       int(width * .024)), fill=CREAM, spacing=8)
    footer(d, width, height, margin)
    output.parent.mkdir(parents=True, exist_ok=True)
    im.convert("RGB").save(output, optimize=True)


def build_growth() -> dict:
    scene = json.loads((ROOT / "video" / ".cache" / "scene_data.json").read_text())
    counts = [len(level) for level in scene["nested"]]
    assert counts == [1, 64, 4096]
    specs = {
        "growth_landscape_1920x1080.png": (1920, 1080),
        "growth_portrait_1080x1350.png": (1080, 1350),
    }
    outdir = OUT / "growth"
    for name, size in specs.items():
        growth(size, outdir / name)
    outputs = sorted(outdir.glob("*.png"))
    receipt = {
        "asset_family": "I06 one tile to a space-filling patch",
        "source_commit": json.loads(PIN.read_text())["source_commit"],
        "nested_counts": counts,
        "inputs": {str(path.relative_to(ROOT)): sha256(path)
                   for path in [TILE, GROWTH_64, GROWTH_4096]},
        "footer": FOOTER,
        "outputs": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size,
                                                   "sha256": sha256(path),
                                                   "dimensions": list(Image.open(path).size)}
                    for path in outputs},
    }
    (OUT / "growth_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def argument_diagram(im: Image.Image, box: tuple[int, int, int, int]) -> None:
    d = ImageDraw.Draw(im)
    x0, y0, x1, y1 = box
    width = x1 - x0
    labels = [("T", "p"), ("D(T)", "p/2"), ("D²(T)", "p/4")]
    cell = width / 3.35
    gap = (width - 3 * cell) / 2
    for i, (top, bottom) in enumerate(labels):
        left = x0 + i * (cell + gap)
        right = left + cell
        d.rounded_rectangle((left, y0, right, y1), radius=max(5, int(cell // 15)),
                            fill=NAVY, outline="#405276", width=2)
        d.text(((left + right) / 2, y0 + (y1 - y0) * .28), top,
               font=font(max(12, int(cell * .11)), True), fill=CREAM, anchor="mm")
        d.text(((left + right) / 2, y0 + (y1 - y0) * .70), bottom,
               font=font(max(11, int(cell * .10)), True), fill=GOLD, anchor="mm")
        if i < 2:
            ax = right + gap / 2
            ay = (y0 + y1) / 2
            d.line((ax - gap * .25, ay, ax + gap * .25, ay), fill=GOLD, width=3)
            d.polygon(((ax + gap * .25, ay), (ax + gap * .05, ay - 7),
                       (ax + gap * .05, ay + 7)), fill=GOLD)


def infographic_card(im: Image.Image, box: tuple[int, int, int, int],
                     number: str, title: str, kind: str) -> None:
    d = ImageDraw.Draw(im)
    x0, y0, x1, y1 = box
    width, height = x1 - x0, y1 - y0
    pad = max(20, int(width * .04))
    d.rounded_rectangle(box, radius=max(12, width // 35), fill="#202d4d",
                        outline="#405276", width=max(2, width // 500))
    d.ellipse((x0 + pad, y0 + pad, x0 + pad + 48, y0 + pad + 48), fill=GOLD)
    d.text((x0 + pad + 24, y0 + pad + 24), number, font=font(23, True), fill=NAVY, anchor="mm")
    title_face = fit_text(d, title, width - 2 * pad - 64, max(18, int(width * .033)), bold=True)
    d.text((x0 + pad + 66, y0 + pad + 24), title, font=title_face, fill=CREAM, anchor="lm")
    art_top = y0 + pad + 66
    note_size = max(13, min(22, width // 33))
    note_face = font(note_size)
    if kind == "tile":
        add_tile(im, (x0 + pad, art_top, x1 - pad, y1 - int(height * .20)), TILE)
        copy = "One connected, unmarked solid. The overlay identifies its 192 tiny geometric bumps and dents."
    elif kind == "space":
        main = (x0 + pad, art_top, x1 - pad, y0 + int(height * .70))
        rounded_image(im, ASSEMBLY_8, main, 10)
        d.rounded_rectangle((main[0] + 10, main[1] + 10, main[0] + min(310, width * .65), main[1] + 44),
                            radius=7, fill=(27, 37, 64, 225))
        d.text((main[0] + 20, main[1] + 27), "8 COMPATIBLE COPIES · ONE HIDDEN CENTRALLY",
               font=fit_text(d, "8 COMPATIBLE COPIES · ONE HIDDEN CENTRALLY", width * .60, 14, bold=True),
               fill=CREAM, anchor="lm")
        copy = "The eight-copy doubled-chair rule iterates, producing arbitrarily large compatible patches."
    elif kind == "control":
        mid = x0 + width // 2
        add_tile(im, (x0 + pad, art_top, mid, y1 - int(height * .22)), PLAIN_TILE)
        rounded_image(im, PERIODIC_VIEW, (mid, art_top + 10, x1 - pad, y1 - int(height * .24)), 8)
        copy = "Remove the features and the plain seven-cube chair admits a lattice-periodic tiling."
    elif kind == "proof":
        argument_diagram(im, (x0 + pad, art_top + int(height * .06), x1 - pad,
                              art_top + int(height * .33)))
        copy = "Unique parent recognition makes every hypothetical period halve at every level. A nonzero integer vector cannot survive indefinitely."
    else:
        raise ValueError(kind)
    note_y = y1 - int(height * .17)
    draw_wrapped(d, (x0 + pad, note_y), copy, note_face, MUTED, width - 2 * pad,
                 spacing=max(4, note_size // 4))


def utilities_panel(im: Image.Image, box: tuple[int, int, int, int]) -> None:
    d = ImageDraw.Draw(im)
    x0, y0, x1, y1 = box
    width, height = x1 - x0, y1 - y0
    d.rounded_rectangle(box, radius=max(12, width // 80), fill=CREAM, outline=GOLD,
                        width=max(2, width // 700))
    pad = max(20, int(width * .025))
    items = [("VIEWER", "viewer/"), ("NOTEBOOK", "notebook/"),
             ("AI REVIEW", "reader/downloads/"), ("PAPER", "paper/"),
             ("EXACT SOLID", "solid/r44_solid.json")]
    gap = max(8, width // 100)
    if width / height > 6:
        copy_width = width * .29
        d.text((x0 + pad, y0 + pad), "5  VERIFY IT YOURSELF",
               font=fit_text(d, "5  VERIFY IT YOURSELF", copy_width, max(20, int(height * .14)), bold=True), fill=NAVY)
        draw_wrapped(d, (x0 + pad, y0 + pad + int(height * .23)),
                     "See it, run it, or ask your own AI.", font(max(13, int(height * .075))),
                     "#5d6478", int(copy_width))
        items_left = x0 + width * .32
        item_width = (x1 - pad - items_left - 4 * gap) / 5
        top, bottom = y0 + pad, y1 - pad
    else:
        d.text((x0 + pad, y0 + pad), "5  VERIFY IT YOURSELF", font=font(max(20, int(height * .12)), True), fill=NAVY)
        d.text((x0 + pad, y0 + pad + int(height * .17)),
               "See the object, run the checks, or hand the evidence to your own AI.",
               font=fit_text(d, "See the object, run the checks, or hand the evidence to your own AI.",
                             width - 2 * pad, max(16, int(height * .08))), fill="#5d6478")
        items_left = x0 + pad
        item_width = (width - 2 * pad - 4 * gap) / 5
        top = y0 + int(height * .48)
        bottom = y1 - pad
    for i, (name, path) in enumerate(items):
        left = items_left + i * (item_width + gap)
        right = left + item_width
        d.rounded_rectangle((left, top, right, bottom), radius=max(6, int(item_width // 18)), fill=NAVY2)
        d.text(((left + right) / 2, top + (bottom - top) * .36), name,
               font=fit_text(d, name, item_width - 16, max(11, int(height * .075)), bold=True),
               fill=GOLD, anchor="mm")
        d.text(((left + right) / 2, top + (bottom - top) * .68), path,
               font=fit_text(d, path, item_width - 16, max(9, int(height * .055))),
               fill=CREAM, anchor="mm")


def infographic(size: tuple[int, int], output: Path) -> None:
    width, height = size
    im = simple_background(size)
    d = ImageDraw.Draw(im)
    margin = max(45, int(min(width, height) * .045))
    title = "Why Chair44 is remarkable"
    title_size = int(min(width, height) * .06)
    d.text((margin, margin), title,
           font=fit_text(d, title, width - 2 * margin, title_size, bold=True, serif=True), fill=CREAM)
    claim = "One shape. It tiles space. No tiling has a translation period."
    d.text((margin, margin + title_size * 1.3), claim,
           font=fit_text(d, claim, width - 2 * margin, int(title_size * .42), bold=True), fill=GOLD)
    landscape = width / height > 1.3
    cards = [("1", "ONE SHAPE", "tile"), ("2", "IT TILES SPACE", "space"),
             ("3", "THE CONTROL REPEATS", "control"), ("4", "WHY NO PERIOD SURVIVES", "proof")]
    if landscape:
        top, bottom = int(height * .20), int(height * .74)
        gap = int(width * .012)
        card_width = (width - 2 * margin - 3 * gap) / 4
        for i, args in enumerate(cards):
            x0 = margin + i * (card_width + gap)
            infographic_card(im, (int(x0), top, int(x0 + card_width), bottom), *args)
        utilities_panel(im, (margin, int(height * .77), width - margin, int(height * .93)))
    else:
        top = int(height * .16)
        row_gap = int(height * .018)
        col_gap = int(width * .025)
        card_width = (width - 2 * margin - col_gap) / 2
        card_height = int(height * .255)
        for i, args in enumerate(cards):
            row, col = divmod(i, 2)
            x0 = margin + col * (card_width + col_gap)
            y0 = top + row * (card_height + row_gap)
            infographic_card(im, (int(x0), int(y0), int(x0 + card_width), int(y0 + card_height)), *args)
        utilities_panel(im, (margin, int(height * .72), width - margin, int(height * .93)))
    footer(d, width, height, margin)
    output.parent.mkdir(parents=True, exist_ok=True)
    rgb = im.convert("RGB")
    rgb.save(output, optimize=True)
    rgb.save(output.with_suffix(".pdf"), "PDF", resolution=150)


def build_infographic() -> dict:
    specs = {
        "why_chair44_portrait_2000x2500.png": (2000, 2500),
        "why_chair44_wide_2400x1350.png": (2400, 1350),
    }
    outdir = OUT / "infographic"
    for name, size in specs.items():
        infographic(size, outdir / name)
    outputs = sorted(path for path in outdir.iterdir() if path.suffix in (".png", ".pdf"))
    receipt = {
        "asset_family": "I02 why Chair44 is remarkable",
        "source_commit": json.loads(PIN.read_text())["source_commit"],
        "inputs": {str(path.relative_to(ROOT)): sha256(path)
                   for path in [TILE, PLAIN_TILE, ASSEMBLY_8, PERIODIC_VIEW]},
        "footer": FOOTER,
        "outputs": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size,
                                                   "sha256": sha256(path)} for path in outputs},
    }
    (OUT / "infographic_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("target", choices=("hero", "comparison", "growth", "infographic"), default="hero", nargs="?")
    args = parser.parse_args()
    pin = json.loads(PIN.read_text())
    expected = pin["canonical_sha256"]["solid/r44_solid.json"]
    assert sha256(SOLID) == expected
    if args.target == "comparison":
        print(json.dumps(build_comparison(), indent=2))
        return
    if args.target == "growth":
        print(json.dumps(build_growth(), indent=2))
        return
    if args.target == "infographic":
        print(json.dumps(build_infographic(), indent=2))
        return
    outputs = build_hero()
    receipt = {
        "asset_family": "I04 discovery hero",
        "source_commit": pin["source_commit"],
        "canonical_solid_sha256": expected,
        "tile_render_sha256": sha256(TILE),
        "exact_tile_render_sha256": sha256(EXACT_TILE),
        "decorative_background_sha256": sha256(BACKGROUND),
        "geometry_policy": "Chair44 is the pinned exact mesh with source-derived flat polarity glyphs rendered just above every feature base; the generated background never supplies geometry or text.",
        "feature_map": "All 192 glyph centres and coefficient signs are read from canonical rational JSON. Filled coral denotes bumps and hollow sky denotes dents; glyphs are annotations.",
        "footer": FOOTER,
        "outputs": outputs,
    }
    (OUT / "hero_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
