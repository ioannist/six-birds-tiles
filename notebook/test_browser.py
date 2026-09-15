"""Exercise the actual HTML outputs of an executed notebook in Chromium.

Optional test dependency: playwright and its Chromium installation. This tests
local browser rendering, not Colab hosting or the mathematical theorem.
"""
import argparse
import json
from pathlib import Path

from playwright.sync_api import sync_playwright


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("notebook", type=Path)
    parser.add_argument("--out", type=Path, default=Path("/tmp/r44-browser-test"))
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    nb = json.loads(args.notebook.read_text())
    outputs = [o["data"]["text/html"] for cell in nb["cells"] for o in cell.get("outputs", [])
               if "text/html" in o.get("data", {})]
    outputs = ["".join(o) if isinstance(o,list) else o for o in outputs]
    frames = [o for o in outputs if "<iframe" in o]
    assert len(frames) == 3, f"Expected viewer, collision and parent displays, got {len(frames)}"
    report = {"scope":"Local Chromium only; no hosted-Colab claim", "frames":[]}
    with sync_playwright() as playwright:
        browser = playwright.chromium.launch(args=["--no-sandbox", "--enable-unsafe-swiftshader", "--use-angle=swiftshader"])
        page = browser.new_page(viewport={"width":1200,"height":740})
        errors=[]
        page.on("pageerror", lambda error: errors.append(str(error)))
        for i, markup in enumerate(frames):
            page.set_content(markup)
            frame = page.frames[1]
            frame.wait_for_selector("canvas", timeout=30000)
            assert frame.locator("canvas").evaluate("c => c.width > 0 && c.height > 0")
            if i == 0:
                frame.locator("#cousinBtn").click()
                frame.locator("#vLattice").click()
                assert "100" in frame.locator("#meterOut").inner_text()
                frame.locator('[data-view="p64"]').click()
                frame.locator("#coarsen").click()
                assert frame.locator("#coarsenNote").inner_text()
                frame.locator('[data-view="tile"]').click()
                frame.locator('[data-look="diagram"]').click()
                frame.locator("#truescale").check()
            else:
                canvas=frame.locator("canvas")
                bounds=canvas.bounding_box()
                page.mouse.move(bounds["x"]+250,bounds["y"]+300)
                page.mouse.down(); page.mouse.move(bounds["x"]+350,bounds["y"]+300); page.mouse.up()
            page.screenshot(path=str(args.out/f"frame-{i}.png"))
            report["frames"].append({"index":i,"canvas":True,"interaction":True})
        browser.close()
    assert not errors, errors
    report.update(status="PASS",page_errors=errors)
    (args.out/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
