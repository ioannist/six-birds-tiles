#!/usr/bin/env python3
"""Build the visual Chair44 reconstruction and priority plate."""
from __future__ import annotations

import base64
from datetime import datetime, timezone
import hashlib
import html
from io import BytesIO
import json
from pathlib import Path

import cairosvg
import qrcode
from PIL import Image

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "media"
OUT = HERE / "output" / "reconstruction"
RAW = HERE / "source" / "numbered_views_raw"
CROPPED = HERE / "source" / "numbered_views"
SOLID_PATH = ROOT / "solid" / "r44_solid.json"
PIN_PATH = ROOT / "reader" / "pin.json"
HERO_PATH = HERE / "source" / "feature_map" / "000090.png"

W, H = 7000, 4949
NAVY, NAVY2, CREAM = "#1b2540", "#26325a", "#f4ecdf"
MUTED, GOLD, CORAL, SKY = "#c9cfe0", "#f3b53a", "#e8563f", "#5aa9e6"
INK = "#18223b"
FOOTER = "Ioannis Tsiokos · with ChatGPT Astra + Six Birds Theory · EmergenceCalculus.com/r44"
GENERATED = datetime.now(timezone.utc).strftime("%Y-%m-%d UTC")
VIEWS = [
    ("px", "+X", [4, 5, 6, 7]), ("nx", "−X", [0, 1, 2, 3]),
    ("py", "+Y", [10, 11, 14, 15]), ("ny", "−Y", [8, 9, 12, 13]),
    ("pz", "+Z", [17, 19, 21, 23]), ("nz", "−Z", [16, 18, 20, 22]),
]


def digest(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def esc(value: object) -> str:
    return html.escape(str(value))


def png_uri(path: Path, crop_alpha: bool = False) -> str:
    image = Image.open(path).convert("RGBA")
    if crop_alpha and (box := image.getchannel("A").getbbox()):
        image = image.crop(box)
    data = BytesIO()
    image.save(data, "PNG", optimize=True)
    return "data:image/png;base64," + base64.b64encode(data.getvalue()).decode()


def qr_uri(url: str) -> str:
    qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M,
                       box_size=7, border=3)
    qr.add_data(url)
    qr.make(fit=True)
    image = qr.make_image(fill_color=NAVY, back_color=CREAM).convert("RGB")
    data = BytesIO()
    image.save(data, "PNG")
    return "data:image/png;base64," + base64.b64encode(data.getvalue()).decode()


def text(x: float, y: float, copy: object, size: int = 32, fill: str = NAVY,
         weight: int = 400, family: str = "DejaVu Sans", anchor: str = "start") -> str:
    return (f'<text x="{x}" y="{y}" font-family="{family}" font-size="{size}" '
            f'font-weight="{weight}" fill="{fill}" text-anchor="{anchor}">{esc(copy)}</text>')


def rect(x: float, y: float, w: float, h: float, fill: str = CREAM,
         stroke: str = GOLD, radius: int = 28, sw: int = 3) -> str:
    return (f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{radius}" '
            f'fill="{fill}" stroke="{stroke}" stroke-width="{sw}"/>')


def prepare_views(solid: dict) -> dict:
    """Crop Blender views and verify that the six projections partition all features."""
    CROPPED.mkdir(parents=True, exist_ok=True)
    canonical = {int(p["role"]): p for p in solid["patches"]}
    seen_roles: set[int] = set()
    seen_panels: set[int] = set()
    prepared = {}
    for directory, label, expected_panels in VIEWS:
        raw_path = RAW / directory / "000090.png"
        projection_path = RAW / directory / "projection.json"
        image = Image.open(raw_path).convert("RGBA")
        projection = json.loads(projection_path.read_text())
        features = projection["features"]
        assert len(features) == 32
        assert sorted({int(row["panel"]) for row in features}) == expected_panels
        for row in features:
            role = int(row["role"])
            assert role not in seen_roles
            assert int(row["coefficient"]) == int(canonical[role]["coefficient"])
            seen_roles.add(role)
            seen_panels.add(int(row["panel"]))
        alpha_box = image.getchannel("A").getbbox()
        assert alpha_box
        pad = 42
        left = max(0, alpha_box[0] - pad)
        top = max(0, alpha_box[1] - pad)
        right = min(image.width, alpha_box[2] + pad)
        bottom = min(image.height, alpha_box[3] + pad)
        cropped = image.crop((left, top, right, bottom))
        cropped_path = CROPPED / f"view_{directory}.png"
        cropped.save(cropped_path, optimize=True)
        points = []
        for row in features:
            px = float(row["x"]) * image.width - left
            py = (1.0 - float(row["y"])) * image.height - top
            assert 0 <= px <= cropped.width and 0 <= py <= cropped.height
            points.append({**row, "px": px, "py": py})
        prepared[directory] = {"label": label, "panels": expected_panels,
                               "path": cropped_path, "width": cropped.width,
                               "height": cropped.height, "features": points}
    assert seen_roles == set(range(192))
    assert seen_panels == set(range(24))
    return prepared


def marker(x: float, y: float, coefficient: int) -> str:
    radius = 28
    if coefficient > 0:
        shape = (f'<circle cx="{x}" cy="{y}" r="{radius}" fill="{CORAL}" '
                 f'stroke="{CREAM}" stroke-width="3"/>')
        colour = CREAM
    else:
        shape = (f'<circle cx="{x}" cy="{y}" r="{radius}" fill="{CREAM}" '
                 f'stroke="{SKY}" stroke-width="6"/>')
        colour = INK
    label = f"{coefficient:+d}".replace("-", "−")
    return shape + text(x, y + 9, label, 23, colour, 700, anchor="middle")


def view_card(x: int, y: int, w: int, h: int, view: dict) -> list[str]:
    parts = [rect(x, y, w, h, CREAM, GOLD, 22, 3),
             text(x + 52, y + 72, f"VIEW FROM {view['label']}", 30, NAVY, 700),
             text(x + w - 52, y + 72,
                  "panels " + " · ".join(f"{p:02d}" for p in view["panels"]),
                  20, "#687086", 500, anchor="end")]
    image_size = min(h - 120, 1330)
    ix = x + (w - image_size) / 2
    iy = y + 92
    parts.append(f'<image href="{png_uri(view["path"])}" x="{ix}" y="{iy}" '
                 f'width="{image_size}" height="{image_size}" preserveAspectRatio="xMidYMid meet"/>')
    sx = image_size / view["width"]
    sy = image_size / view["height"]
    for row in view["features"]:
        parts.append(marker(ix + row["px"] * sx, iy + row["py"] * sy,
                            int(row["coefficient"])))
    return parts


def build_svg(pin: dict, views: dict, source_url: str) -> str:
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="841mm" height="594mm" viewBox="0 0 {W} {H}">',
             f'<rect width="{W}" height="{H}" fill="{NAVY}"/>']
    parts += [text(100, 145, "Chair44", 98, CREAM, 700, "DejaVu Serif"),
              text(625, 145, "(R44)", 98, GOLD, 700, "DejaVu Serif"),
              text(100, 235, "VISUAL RECONSTRUCTION PLATE · EVERY BUMP AND DENT MARKED", 31, MUTED, 700),
              text(6900, 90, "PROOF SUBMISSION", 25, GOLD, 700, anchor="end"),
              text(6900, 135, f"Generated {GENERATED}", 22, MUTED, anchor="end"),
              text(6900, 175, f"Pinned commit {pin['source_commit'][:12]}", 22, MUTED, anchor="end")]

    parts.append(rect(90, 315, 3250, 1450, NAVY2, "#405276", 28, 3))
    parts += [text(145, 385, "THE TILE", 31, GOLD, 700),
              text(145, 432, "Exact solid with enlarged feature annotations", 22, MUTED),
              f'<image href="{png_uri(HERO_PATH, True)}" x="260" y="435" width="2920" height="1250" preserveAspectRatio="xMidYMid meet"/>']

    parts.append(rect(3380, 315, 3530, 1450, CREAM, GOLD, 28, 3))
    parts += [text(3450, 405, "HOW TO READ THE SIX VIEWS", 38, NAVY, 700),
              text(3450, 485, "Every feature appears once below, on its outward-facing side.", 27, NAVY),
              '<circle cx="3500" cy="585" r="28" fill="%s" stroke="%s" stroke-width="4"/>' % (CORAL, CREAM),
              text(3500, 594, "+7", 22, CREAM, 700, anchor="middle"),
              text(3560, 594, "coral +number  =  outward bump", 28, NAVY, 700),
              '<circle cx="3500" cy="675" r="28" fill="%s" stroke="%s" stroke-width="7"/>' % (CREAM, SKY),
              text(3500, 684, "−7", 22, NAVY, 700, anchor="middle"),
              text(3560, 684, "blue −number  =  inward dent", 28, NAVY, 700),
              text(3450, 800, "HEIGHT", 23, CORAL, 700),
              text(3660, 800, "|number| / 10,000, normal to the face", 25, NAVY),
              text(3450, 875, "BASE", 23, CORAL, 700),
              text(3660, 875, "square, side 1/50", 25, NAVY),
              text(3450, 950, "SITES", 23, CORAL, 700),
              text(3660, 950, "relative to each unit-panel centre:", 25, NAVY),
              text(3660, 1002, "(±1/8, ±1/4) and (±1/4, ±1/8)", 25, NAVY, 600, "DejaVu Sans Mono"),
              text(3450, 1110, "CARRIER", 23, CORAL, 700),
              text(3660, 1110, "seven unit cubes in a 2×2×2 block; the +X,+Y,+Z corner is absent", 24, NAVY),
              text(3450, 1245, "The matching pattern forces the hierarchy behind the proof.", 29, NAVY, 700),
              text(3450, 1300, "Feature size is a convenient realization; matching is what matters.", 24, "#5d6478"),
              text(3450, 1400, "Paper theorem", 22, GOLD, 700),
              text(3450, 1450, "Chair44 tiles space, and no tiling by it has a symmetry of infinite order.", 25, NAVY),
              text(3450, 1560, "Six face-on views · 24 panels · 192 marked features", 25, CORAL, 700)]

    card_w, card_h = 2220, 1450
    for i, (directory, _label, _panels) in enumerate(VIEWS):
        x = 90 + (i % 3) * 2290
        y = 1815 + (i // 3) * 1490
        parts.extend(view_card(x, y, card_w, card_h, views[directory]))

    json_hash = digest(SOLID_PATH)
    parts += [text(110, 4820, f"Canonical JSON  {json_hash}", 18, MUTED, family="DejaVu Sans Mono"),
              text(110, 4860, f"Commit  {pin['source_commit']}", 18, MUTED, family="DejaVu Sans Mono"),
              f'<image href="{qr_uri(source_url)}" x="6550" y="4682" width="210" height="210"/>',
              text(6655, 4920, "PINNED JSON", 16, GOLD, 700, anchor="middle"),
              text(3500, 4920, FOOTER, 21, MUTED, anchor="middle"),
              '</svg>']
    return "".join(parts)


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    solid = json.loads(SOLID_PATH.read_text())
    pin = json.loads(PIN_PATH.read_text())
    assert digest(SOLID_PATH) == pin["canonical_sha256"]["solid/r44_solid.json"]
    assert len(solid["patches"]) == 192
    views = prepare_views(solid)
    source_url = ("https://raw.githubusercontent.com/ioannist/six-birds-tiles/"
                  f"{pin['source_commit']}/solid/r44_solid.json")
    svg = build_svg(pin, views, source_url)
    svg_path = OUT / "chair44_visual_reconstruction_plate_r2.svg"
    pdf_path = OUT / "chair44_visual_reconstruction_plate_r2.pdf"
    web_path = OUT / "chair44_visual_reconstruction_plate_r2_web_4000.png"
    master_path = OUT / "chair44_visual_reconstruction_plate_r2_9933x7016.png"
    svg_path.write_text(svg)
    # Preserve the physical 841 mm × 594 mm dimensions declared by the SVG.
    cairosvg.svg2pdf(bytestring=svg.encode(), write_to=str(pdf_path))
    cairosvg.svg2png(bytestring=svg.encode(), write_to=str(web_path),
                     output_width=4000, output_height=round(4000 * H / W))
    cairosvg.svg2png(bytestring=svg.encode(), write_to=str(master_path),
                     output_width=9933, output_height=7016)
    receipt = {
        "plate": "Chair44 visual reconstruction plate R2",
        "generated": GENERATED,
        "source_commit": pin["source_commit"],
        "canonical_sha256": digest(SOLID_PATH),
        "all_192_features_marked_exactly_once": True,
        "all_24_panels_shown_exactly_once": True,
        "view_feature_counts": {d: len(views[d]["features"]) for d, _, _ in VIEWS},
        "outputs": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size,
                                                    "sha256": digest(path)}
                    for path in (svg_path, pdf_path, web_path, master_path)},
        "pdf_note": "Vector A1 PDF generated from SVG; PDF/A conformance is not certified.",
    }
    (OUT / "chair44_visual_reconstruction_plate_r2_receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
