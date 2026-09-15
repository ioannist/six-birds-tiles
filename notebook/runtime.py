"""U4 presentation and session support; embedded into the generated notebook.

Geometric predicates are executed from the pinned proof packets. Coordinates
are converted to floats only at the final display boundary.
"""
import contextlib
import copy
import datetime
from fractions import Fraction
import gzip
import hashlib
import html
import io
import json
import os
from pathlib import Path
import platform
import runpy
import subprocess
import sys
import tarfile
import tempfile
import time

from IPython.display import HTML, Markdown, display


class Session:
    def __init__(self, pin, claim_map):
        self.pin = pin
        self.claim_map = claim_map
        self.directory = Path(tempfile.mkdtemp(prefix="r44-reader-"))
        self.source = self.directory / "source"
        self.source.mkdir()
        self.receipt = {
            "notice": "Unsigned session record. Records only this session's executions; this utility is not evidence for the theorem.",
            "commit": pin["source_commit"], "mathematical_baseline_commit": pin["mathematical_baseline_commit"],
            "canonical_sha256": {}, "python": sys.version, "platform": platform.platform(),
            "host": "Google Colab" if "google.colab" in sys.modules else platform.node(),
            "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "cells": {}, "lean_ran": False, "replay_report": None,
        }
        self.receipt_path = self.directory / "receipt.json"
        self.save()

    def save(self):
        self.receipt_path.write_text(json.dumps(self.receipt, indent=2) + "\n")

    def run(self, name, action, tier="T2"):
        start = time.monotonic()
        artifact_keys = {
            "finite_replay": "replay_report", "collision_witness": "collision_selection",
            "parent_certificate": "parent_selection", "atlas_equality": "atlas_difference",
            "mutation_controls": "mutation_controls", "periodic_controls": "periodic_controls",
            "companion_census": "companion_census", "selected_mutation": "selected_mutation",
        }
        if name in artifact_keys:
            self.receipt.pop(artifact_keys[name], None)
        record = {"tier": tier, "status": "running"}
        self.receipt["cells"][name] = record
        self.save()
        try:
            result = action()
            record["status"] = "PASS"
            return result
        except BaseException as exc:
            record.update(status="interrupted" if isinstance(exc, KeyboardInterrupt) else "FAIL", error=str(exc))
            raise
        finally:
            record["seconds"] = round(time.monotonic() - start, 3)
            self.save()

    def command(self, args, cwd=None, log="command", timeout=240):
        proc = subprocess.run(args, cwd=cwd or self.source, text=True,
                              capture_output=True, timeout=timeout)
        (self.directory / (log + ".log")).write_text(proc.stdout + proc.stderr)
        if proc.returncode:
            raise RuntimeError(f"{log} exited {proc.returncode}:\n{proc.stderr[-3000:]}")
        return proc.stdout

    def prepare(self):
        def action():
            repo = os.environ.get("R44_SOURCE_REPO")
            if repo is None:
                repo = str(self.directory / "git")
                self.command(["git", "init", "--quiet", repo], log="git-init")
                self.command(["git", "-C", repo, "remote", "add", "origin",
                              "https://github.com/ioannist/six-birds-tiles.git"], log="git-remote")
                self.command(["git", "-C", repo, "fetch", "--depth=1", "--filter=blob:none",
                              "origin", self.pin["source_commit"]], log="git-fetch", timeout=600)
            commit = subprocess.check_output(["git", "-C", repo, "rev-parse",
                                               self.pin["source_commit"] + "^{commit}"], text=True).strip()
            if commit != self.pin["source_commit"]:
                raise ValueError("Source commit mismatch")
            paths = ["solid", "certificates", "verify", "simulations", "viewer",
                     "paper/tex", "paper/CLAIMS_LEDGER.md", "lean/R44/build_axioms.log",
                     "lean/R44/negative_control.log", "lean/R44/HYPOTHESES.md", "lean/R44/AXIOMS.md"]
            archive = self.directory / "source.tar"
            with archive.open("wb") as out:
                subprocess.run(["git", "-C", repo, "archive", commit, "--", *paths], stdout=out, check=True)
            forbidden = {".git", ".codex", "offgit", "history", "archive", ".lake", "review", "TILE_DISCOVERY_THREAD.txt"}
            with tarfile.open(archive) as tar:
                for member in tar:
                    parts = Path(member.name).parts
                    if any(part in forbidden for part in parts):
                        continue
                    if member.name.startswith("/") or ".." in parts or not (member.isfile() or member.isdir()):
                        raise ValueError("Unsafe source archive member: " + member.name)
                    dest = self.source / member.name
                    if member.isdir():
                        dest.mkdir(parents=True, exist_ok=True)
                    else:
                        dest.parent.mkdir(parents=True, exist_ok=True)
                        dest.write_bytes(tar.extractfile(member).read())
            archive.unlink()
            self.check_hashes()
            expected_sources = {"paper/CLAIMS_LEDGER.md": self.claim_map["ledger_sha256"],
                                "lean/R44/build_axioms.log": self.claim_map["axiom_log_sha256"],
                                **self.claim_map["tex_sha256"]}
            for path, digest in expected_sources.items():
                if hashlib.sha256((self.source/path).read_bytes()).hexdigest() != digest:
                    raise ValueError("Evidence-map source mismatch: " + path)
            # Only immutable source files are copied; output-producing checks run here.
            self.work = self.directory / "work"
            import shutil
            shutil.copytree(self.source, self.work)
            display(Markdown("**Source snapshot** `" + commit + "`"))
            display(Markdown("\n".join(f"- `{path}`: `{digest}`" for path, digest in self.receipt["canonical_sha256"].items())))
        self.run("setup", action, "T2 (file identity)")

    def check_hashes(self):
        for path, expected in self.pin["canonical_sha256"].items():
            actual = hashlib.sha256((self.source / path).read_bytes()).hexdigest()
            if actual != expected:
                raise ValueError("Canonical digest mismatch: " + path)
            self.receipt["canonical_sha256"][path] = actual
        self.save()

    def replay(self):
        def action():
            self.command([sys.executable, "verify/replay.py"], cwd=self.work, log="replay")
            report = json.loads((self.work / "verify/replay_report.json").read_text())
            self.receipt["replay_report"] = report
            if report["status"] != "PASS":
                raise ValueError("Replay did not pass")
            if self.receipt["canonical_sha256"] != report["canonical_sha256"]:
                raise ValueError("Replay digest mismatch")
            display(Markdown("**T2 — finite replay** · " + str(report["seconds"]) + " seconds in this session"))
            display(Markdown("\n".join("- `" + r["packet"] + "`: exit " + str(r["returncode"]) for r in report["steps"])))
        self.run("finite_replay", action)

    def module(self, relative):
        # Some canonical scripts execute on import and produce JSON files.
        capture = io.StringIO()
        with contextlib.redirect_stdout(capture):
            result = runpy.run_path(str(self.work / relative))
        (self.directory / (Path(relative).stem + ".log")).write_text(capture.getvalue())
        return result

    def companions(self):
        def action():
            output = self.directory / "fresh-alignment.json"
            output.unlink(missing_ok=True)
            self.command([sys.executable, "verify/packets/r44_unrestricted_alignment/src/verify_alignment.py",
                          "--output", str(output)], cwd=self.work, log="alignment")
            report = json.loads(output.read_text())
            if report["status"] != "PASS":
                raise ValueError("Alignment checker did not pass")
            self.receipt["companion_census"] = report
            display(HTML("<details><summary>T2 — inspect the fresh alignment report</summary><pre>" + html.escape(json.dumps(report, indent=2)) + "</pre></details>"))
        self.run("companion_census", action)

    def viewer(self):
        text = (self.source / "viewer/index.html").read_text()
        for name in ["vendor/three.min.js", "r44_data.js"]:
            code = (self.source / "viewer" / name).read_text().replace("</script", "<\\/script")
            text = text.replace('<script src="' + name + '"></script>', "<script>" + code + "</script>")
        data_text = (self.source / "viewer/r44_data.js").read_text()
        for path in ["solid/r44_solid.json", "certificates/candidate_certificate.json"]:
            if self.pin["canonical_sha256"][path] not in data_text:
                raise ValueError("Viewer source hash mismatch")
        self.iframe(text, "R44 viewer")

    def iframe(self, document, title):
        display(HTML('<iframe title="' + html.escape(title) + '" sandbox="allow-scripts" '
                     'style="width:100%;height:660px;border:0" srcdoc="' + html.escape(document, quote=True) + '"></iframe>'))

    def mesh_display(self, poses, box=None):
        """Display only: input poses are exact rational row-matrix isometries."""
        solid = json.loads((self.source / "solid/r44_solid.json").read_text())
        vertices = [list(map(Fraction, p)) for p in solid["vertices"]]
        meshes = []
        for matrix, translation in poses:
            transformed = [[sum(Fraction(matrix[i][j])*v[j] for j in range(3)) + Fraction(translation[i])
                            for i in range(3)] for v in vertices]
            meshes.append([float(x) for tri in solid["triangles"] for k in tri for x in transformed[k]])
        payload = json.dumps({"meshes": meshes, "box": [[float(x) for x in side] for side in box] if box else None})
        three = (self.source / "viewer/vendor/three.min.js").read_text().replace("</script", "<\\/script")
        script = """
const data=PAYLOAD, scene=new THREE.Scene(); scene.background=new THREE.Color('#1b2540');
const camera=new THREE.PerspectiveCamera(40,innerWidth/innerHeight,.01,1000);
const renderer=new THREE.WebGLRenderer({antialias:true}); renderer.setSize(innerWidth,innerHeight); document.body.append(renderer.domElement);
scene.add(new THREE.AmbientLight(0xffffff,.8)); const light=new THREE.DirectionalLight(0xffffff,.8); light.position.set(5,8,10); scene.add(light);
const group=new THREE.Group(); scene.add(group);
data.meshes.forEach((positions,i)=>{const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));g.computeVertexNormals();group.add(new THREE.Mesh(g,new THREE.MeshPhongMaterial({color:[0x5aa9e6,0xe8563f,0xf3b53a][i%3],transparent:true,opacity:.4,side:THREE.DoubleSide})));});
if(data.box){const [lo,hi]=data.box;const g=new THREE.BoxGeometry(...hi.map((x,i)=>x-lo[i]));const b=new THREE.Mesh(g,new THREE.MeshBasicMaterial({color:0xf3b53a}));b.position.set(...hi.map((x,i)=>(x+lo[i])/2));group.add(b);}
const bounds=new THREE.Box3().setFromObject(group),center=bounds.getCenter(new THREE.Vector3());group.position.sub(center);
const pivot=new THREE.Group();scene.add(pivot);pivot.add(group);
const radius=Math.max(2,bounds.getSize(new THREE.Vector3()).length());camera.position.set(radius*.7,radius*.5,radius);camera.lookAt(0,0,0);
let down=false,x=0;renderer.domElement.onpointerdown=e=>{down=true;x=e.clientX;renderer.domElement.setPointerCapture(e.pointerId)};renderer.domElement.onpointerup=()=>down=false;renderer.domElement.onpointermove=e=>{if(down){pivot.rotation.y+=(e.clientX-x)*.01;x=e.clientX}};
renderer.domElement.onwheel=e=>{e.preventDefault();camera.position.multiplyScalar(e.deltaY>0?1.08:.92)};
onresize=()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight)};
(function loop(){requestAnimationFrame(loop);renderer.render(scene,camera)})();
""".replace("PAYLOAD", payload)
        self.iframe('<html><body style="margin:0;overflow:hidden"><div style="position:absolute;color:white;padding:12px;font:14px sans-serif">Display only · floats · true geometry · drag to rotate, scroll to zoom</div><script>' + three + '</script><script>' + script + '</script></body></html>', "Exact certificate data displayed in 3D")

    def collision(self, record_index=0, partner_index=0):
        def action():
            if not hasattr(self, "core"):
                self.core = self.module("verify/packets/r44_unrestricted_alignment/src/replay_core_boxes.py")
            with gzip.open(self.source / "certificates/collision_core_witnesses.jsonl.gz", "rt") as stream:
                records = (json.loads(line) for line in stream)
                record = next((r for i, r in enumerate(records) if i == record_index), None)
            if record is None:
                raise ValueError("Record index out of range")
            g, t = map(tuple, record["normalized_other"])
            h, u, ia, ib, claimed_lo, claimed_hi = record["overlaps"][partner_index]
            h, u = tuple(h), tuple(u)
            a = self.core["selected_box"](g,t,ia); b = self.core["selected_box"](h,u,ib)
            lo = tuple(max(a[i], b[i]) for i in range(3)); hi = tuple(min(a[i]+8,b[i]+8) for i in range(3))
            self.core["check"](lo == tuple(claimed_lo) and hi == tuple(claimed_hi), "wrong displayed witness")
            lower = tuple(Fraction(50*x+4,400) for x in lo); upper = tuple(Fraction(50*x-4,400) for x in hi)
            self.core["check"](min(upper[i]-lower[i] for i in range(3)) >= Fraction(42,400), "invalid retained core")
            def pose(frame, shift):
                # Packet frames store the signed image of each input basis vector.
                matrix = [[(1 if frame[j]>0 else -1) if abs(frame[j]) == i+1 else 0 for j in range(3)] for i in range(3)]
                return matrix, [Fraction(x,8) for x in shift]
            result = {"record": record_index, "partner": partner_index, "lower": list(map(str,lower)), "upper": list(map(str,upper))}
            self.receipt["collision_selection"] = result
            display(Markdown("**T2 — retained-core collision witness** · yellow box; two implicated copies in blue and coral."))
            display(Markdown("Exact lower corner: `"+str(result["lower"])+"`; upper corner: `"+str(result["upper"])+"`."))
            self.mesh_display([pose(g,t),pose(h,u)], (lower,upper))
        self.run("collision_witness", action)

    def parent(self, shell_index=0):
        def action():
            data = json.loads((self.source / "certificates/candidate_certificate.json").read_text())
            roles = data["role_options"][shell_index]
            if len(roles) != 1:
                raise ValueError("Expected one recorded parent role")
            def pose(p):
                (perm, signs), shift = p
                return [[signs[i] if j==perm[i] else 0 for j in range(3)] for i in range(3)], shift
            display(Markdown(f"**T2 — certificate shell {shell_index}** · recorded role {roles[0]}. This displays the certificate; interactive recognition of a reader's own patch is deferred to U2."))
            self.receipt["parent_selection"] = {"shell":shell_index,"roles":roles,"contacts":data["solutions"][shell_index]}
            display(Markdown("Contact indices: `"+str(data["solutions"][shell_index])+"`"))
            poses = [pose([[[0,1,2],[1,1,1]],[0,0,0]])] + [pose(data["legal_contacts"][i]) for i in data["solutions"][shell_index]]
            self.mesh_display(poses)
        self.run("parent_certificate", action)

    def atlas(self):
        def action():
            namespace = self.module("verify/packets/einstein_macrostate/src/verify.py")
            fine, coarse = namespace["legal"], namespace["coarse"]
            result = {"fine_count":len(fine),"coarse_count":len(coarse),
                      "missing":sorted(fine-coarse),"additional":sorted(coarse-fine)}
            self.receipt["atlas_difference"] = result
            if result["missing"] or result["additional"]:
                raise ValueError("Contact sets differ")
            display(Markdown("**T2 — rescaled parent atlas versus fine atlas**\n\nMissing contacts: **0**. Additional contacts: **0**."))
            display(HTML("<details><summary>Inspect both sets and their differences</summary><pre>"+html.escape(json.dumps({**result,"fine":sorted(fine),"coarse":sorted(coarse)},indent=2))+"</pre></details>"))
        self.run("atlas_equality", action)

    def mutations(self):
        def action():
            root = self.work / "verify/packets/r44_unrestricted_alignment"
            self.command([sys.executable,str(root / "src/test_mutations.py")], cwd=root, log="mutations")
            report = json.loads((root / "results/mutation_controls.json").read_text())
            if len(report["tests"]) != 6 or not all(t["rejected"] for t in report["tests"]):
                raise ValueError("Mutation control failed")
            self.receipt["mutation_controls"] = report
            self.check_hashes()
            display(Markdown("**T2 — all six temporary corruptions rejected.** Canonical inputs retain their original hashes; temporary variants were removed."))
            return report
        return self.run("mutation_controls", action)

    def mutation(self, name="missing_triangle", index=0):
        """Apply the existing six corruption recipes at a reader-selected index.

        Only input construction is adapted from test_mutations.py; the unchanged
        verify_alignment.py judges the result. No geometric predicate is added.
        """
        def action():
            choices = {
                "missing_triangle": ("solid/r44_solid.json", "--solid", "triangles", "nonmanifold mesh edge"),
                "reversed_triangle": ("solid/r44_solid.json", "--solid", "triangles", "unpaired oriented edge"),
                "changed_geometric_apex": ("solid/r44_solid.json", "--solid", "patches", "wrong feature height"),
                "missing_rejection_witness": ("certificates/companion_collision_certificate.json", "--collisions", "witnesses", "duplicate/missing rejection witness"),
                "wrong_companion_quantifier": ("certificates/companion_collision_certificate.json", "--collisions", "witnesses", "incomplete partner quantifier"),
                "missing_registered_contact": ("certificates/candidate_certificate.json", "--registered", "legal_contacts", "survivors not identical to registered 44 atlas"),
            }
            path, flag, field, diagnostic = choices[name]
            data = json.loads((self.source/path).read_text())
            if not 0 <= index < len(data[field]):
                raise ValueError(f"Choose an index between 0 and {len(data[field])-1}")
            if name.startswith("missing_"):
                data[field].pop(index)
            elif name == "reversed_triangle":
                tri = data[field][index]; tri[0], tri[1] = tri[1], tri[0]
            elif name == "wrong_companion_quantifier":
                data[field][index]["possible_partners"] += 1
            else:
                apex = tuple(map(Fraction, data["patches"][index]["apex"]))
                k = next(i for i,v in enumerate(data["vertices"]) if tuple(map(Fraction,v)) == apex)
                data["vertices"][k][0] = str(Fraction(data["vertices"][k][0]) + Fraction(1,100000))
            with tempfile.TemporaryDirectory(dir=self.directory, prefix="mutation-") as tmp:
                altered = Path(tmp)/"altered.json"; altered.write_text(json.dumps(data))
                proc = subprocess.run([sys.executable, str(self.work/"verify/packets/r44_unrestricted_alignment/src/verify_alignment.py"),
                                       flag, str(altered), "--output",str(Path(tmp)/"result.json")], capture_output=True,text=True,timeout=90)
                diagnostics = [diagnostic, "off-center pyramid apex"] if name == "changed_geometric_apex" else [diagnostic]
                actual_diagnostic = next((d for d in diagnostics if ("ValueError: " + d) in proc.stderr), None)
                if proc.returncode == 0 or actual_diagnostic is None:
                    raise RuntimeError("Unexpected mutation result; this is not a successful rejection control:\n" + proc.stderr[-1200:])
                diagnostic = actual_diagnostic
            self.check_hashes()
            self.receipt["selected_mutation"] = {"name":name,"index":index,"diagnostic":diagnostic,"rejected":True,"temporary_copy_removed":True}
            display(Markdown("**T2 — selected mutation rejected:** `"+name+"`, index "+str(index)+".\n\n`ValueError: "+diagnostic+"`\n\nTemporary change removed; canonical hashes unchanged."))
        self.run("selected_mutation", action)

    def controls(self):
        def action():
            try:
                import pysat
            except ImportError:
                self.command([sys.executable,"-m","pip","install","python-sat==1.9.dev15"], log="install-python-sat", timeout=600)
                import pysat
            output = self.directory / "periodic-controls.json"
            self.command([sys.executable,"simulations/periodicity_search.py","--controls","--control-index","7","--out",str(output)], cwd=self.work, log="periodic-controls", timeout=180)
            report = json.loads(output.read_text())
            if len(report["runs"]) != 2 or not all(r["control_passed"] and r["torus"]["sat_witness"] is not None for r in report["runs"]):
                raise ValueError("Periodic controls failed")
            self.receipt["periodic_controls"] = report
            self.receipt["python_sat_version"] = pysat.__version__
            display(Markdown("**T2-adjacent — evidence only, used nowhere in the proof.**"))
            for result in report["runs"]:
                display(Markdown("Periodic control: **"+result["tile"]+"**"))
                display(HTML("<details><summary>Inspect periodic witness</summary><pre>"+html.escape(json.dumps(result["torus"]["sat_witness"],indent=2))+"</pre></details>"))
        self.run("periodic_controls", action, "T2-adjacent (paper §8.1)")

    def sources(self):
        self.run("source_reading", self._sources, "T1/T1n/T3 source records; not executed")

    def _sources(self):
        display(Markdown("**T1 / T1n / T3 — source statements and supplied axiom records. No Lean build runs in this notebook.**"))
        rows = {r["id"]:r for r in self.claim_map["rows"]}
        groups = [
            ("Existence and exhaustion", ["T1", "R8", "R10"], ["R44.existence", "R44.r44_einstein"]),
            ("Registration", ["T10", "A14"], ["R44.unrestricted_alignment_holds"]),
            ("Iterated parents and coarsening", ["T8", "R6", "R7"], ["R44.geometric_hierarchy_unique", "R44.carrier_hierarchy", "R44.parent_atlas_eq_fine"]),
            ("Period halving", ["T2", "T13"], ["R44.period_halving", "R44.no_period", "R44.r44_einstein"]),
        ]
        for title, ids, names in groups:
            display(Markdown("### " + title))
            for claim in ids:
                row = rows[claim]
                display(Markdown("**" + claim + " · " + row["ledger_tier"] + "** — quoted ledger statement:\n\n> " + row["statement"] + "\n\nPaper sections: " + str(row["paper_sections"])))
            for name in names:
                record = self.claim_map["axiom_records"].get(name)
                if record is None:
                    raise ValueError("Missing axiom map declaration: " + name)
                display(HTML('<details><summary>'+html.escape(name)+' — supplied axiom record</summary><pre>'+html.escape(json.dumps(record,indent=2))+'</pre></details>'))
        display(HTML('<details><summary>Complete generated evidence map</summary><pre>'+html.escape(json.dumps(self.claim_map,indent=2))+'</pre></details>'))
        for path in ["paper/tex/sec3_finding.tex","paper/tex/sec5_registration.tex","paper/tex/sec6_hierarchy.tex","paper/tex/sec7_aperiodicity.tex"]:
            display(HTML('<details><summary>Quoted proof source: '+html.escape(path)+'</summary><pre>'+html.escape((self.source/path).read_text())+'</pre></details>'))
        for path in ["lean/R44/build_axioms.log", "lean/R44/negative_control.log"]:
            display(HTML('<details><summary>Supplied record, not a fresh build: '+html.escape(path)+'</summary><pre>'+html.escape((self.source/path).read_text())+'</pre></details>'))

    def download(self):
        self.check_hashes()
        for name in ["setup","finite_replay","viewer","collision_witness","companion_census","parent_certificate","atlas_equality","mutation_controls","selected_mutation","periodic_controls","source_reading"]:
            self.receipt["cells"].setdefault(name,{"status":"skipped"})
        self.save()
        import base64
        data = base64.b64encode(self.receipt_path.read_bytes()).decode()
        display(HTML('<a download="r44-receipt.json" href="data:application/json;base64,'+data+'">Download your session receipt</a>'))
        display(Markdown("Unsigned session record · `lean_ran: false` · " + str(self.receipt_path)))
