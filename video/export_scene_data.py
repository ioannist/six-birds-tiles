#!/usr/bin/env python3
"""Archive pinned inputs, check exact fixtures, then export render-boundary floats."""
import hashlib
import io
import itertools
import json
from fractions import Fraction as F
from pathlib import Path
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CACHE = HERE / '.cache'

def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def main():
    pin = json.loads((HERE / 'source_pin.json').read_text())
    paths = list(pin['canonical_sha256']) + ['simulations/r44.py', 'simulations/patches.py', 'paper/tex']
    archive = subprocess.check_output(['git', 'archive', pin['source_commit'], '--', *paths], cwd=ROOT)
    source = CACHE / 'source'
    source.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
        for m in tf.getmembers():
            assert m.isfile() or m.isdir()
            assert not set(Path(m.name).parts) & {'offgit', 'archive', 'history', '.codex', '.lake', '.agents'}
        tf.extractall(source, filter='data')
    hashes = {p: hashlib.sha256((source / p).read_bytes()).hexdigest() for p in pin['canonical_sha256']}
    assert hashes == pin['canonical_sha256'], 'Canonical identity check failed'
    sys.path.insert(0, str(source / 'simulations'))
    import patches as P
    import r44 as R
    children, legal, solid = P.evidence()
    nested = [P.nested_patch(n) for n in range(3)]
    patch_checks = [P.check_patch(p, legal) for p in nested]
    inclusions = [P.check_nested_pair(n, nested[n], nested[n+1]) for n in range(2)]
    sigma = [P.sigma_depth(n) for n in range(3)]
    for p in sigma:
        P.check_patch(p, legal)
    basis = ((-2,1,0), (-1,-1,-1), (-1,0,2))
    a,b,c = basis
    det = sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3]) for i in range(3))
    residue = lambda x: (x[0]+2*x[1]+4*x[2]) % 7
    assert det == 7 and all(residue(b)==0 for b in basis)
    assert sorted(map(residue, R.CHAIR_CELLS)) == list(range(7))
    lattice = lambda abc: tuple(sum(abc[j]*basis[j][i] for j in range(3)) for i in range(3))
    # Buffered display; the marked central motif has two exact translated copies.
    periodic = [(R.IDENTITY_FRAME,lattice(k)) for k in itertools.product(range(-3,4),range(-2,3),range(-2,3))]
    periodic_set = set(periodic)
    # Exposed surface strip; buffered along the tested translation, visible to camera.
    motif = [(R.IDENTITY_FRAME,lattice((i,-2,0))) for i in range(-1,2)]
    for step in (1,2):
        assert all(R.translate_pose(p, tuple(step*x for x in basis[0])) in periodic_set for p in motif)
    # Exact section at z=3/8 for the two copies separated by -b1.
    center = (F(2),F(1,4),F(3,8))
    shift = (2,-1,0)
    assert not (R.pose_cells(R.ROOT_POSE) & R.pose_cells((R.IDENTITY_FRAME,shift)))
    found = []
    for tr in ((0,0,0),shift):
        matches=[]
        for p in solid['patches']:
            base=[tuple(F(x)+t for x,t in zip(v,tr)) for v in p['base']]
            mean=tuple(sum(v[i] for v in base)/4 for i in range(3))
            if mean == center:
                apex=tuple(F(x)+t for x,t in zip(p['apex'],tr))
                matches.append((p,base,apex))
        assert len(matches)==1
        found.append(matches[0])
    pa,ba,aa=found[0]; pb,bb,ab=found[1]
    ha,hb=aa[0]-center[0],center[0]-ab[0]
    assert ha==F(3,2500) and hb==F(1,5000)
    assert pa['coefficient']>0 and pb['coefficient']>0
    eta=F(solid['base_halfwidth'])
    assert eta==F(1,100)
    # Tent profiles are exact intersections of square pyramids at their midplane.
    section=[]
    for u in (-F(1,40),-eta,F(0),eta,F(1,40)):
        f=max(F(0),1-abs(u)/eta)
        section.append([str(u),str(ha*f),str(-hb*f)])
    assert ha+hb==F(7,5000)>0
    vertices,matnames=P._triangle_materials(solid)
    # Feature flattening uses the same triangulation with apex returned to base centre.
    flattened=list(vertices)
    vi={v:i for i,v in enumerate(vertices)}
    for p in solid['patches']:
        apex=tuple(F(v) for v in p['apex'])
        flat=tuple(sum(F(v[i]) for v in p['base'])/4 for i in range(3))
        flattened[vi[apex]]=flat
    # Plain chair boundary, oriented outward. No interior cube faces.
    pv=[]; pf=[]
    for cell in sorted(R.CHAIR_CELLS):
        for axis in range(3):
            for side in (-1,1):
                neighbor=list(cell); neighbor[axis]+=side
                if tuple(neighbor) in R.CHAIR_CELLS: continue
                u=(axis+1)%3; v=(axis+2)%3
                face=[]
                for du,dv in ((0,0),(1,0),(1,1),(0,1)):
                    point=list(cell); point[axis]+=int(side>0); point[u]+=du; point[v]+=dv
                    face.append(len(pv)); pv.append(point)
                pf.append(face if side>0 else face[::-1])
    data={
        'source_commit':pin['source_commit'],
        'vertices':[[float(x) for x in v] for v in vertices],
        'flat_vertices':[[float(x) for x in v] for v in flattened],
        'triangles':solid['triangles'], 'triangle_kinds':matnames,
        'plain_vertices':pv,'plain_faces':pf,'cells':sorted(R.CHAIR_CELLS),
        'sigma':[[R.pose_json(p) for p in poses] for poses in sigma],
        'nested':[[R.pose_json(p) for p in poses] for poses in nested],
        'periodic':[R.pose_json(p) for p in periodic],
        'periodic_motif':[R.pose_json(p) for p in motif],
        'periodic_basis':basis,'section':section,
        'fixture':{'center':[str(x) for x in center],'translations':[(0,0,0),shift],'heights':[str(ha),str(hb)]},
    }
    dump(CACHE/'scene_data.json',data)
    receipt={**pin,'canonical_identity':'PASS','nested_patches':patch_checks,'inclusions':inclusions,
        'periodic':{'determinant':det,'carrier_residues':sorted(map(residue,R.CHAIR_CELLS)),
        'basis':basis,'buffered_motif_two_translations':'PASS'},
        'restored_contact':{'solid_overlap':'7/5000','section':section,
        'note':'The two solids overlap; the positive pyramid portions need not overlap each other.'},
        'render_data_sha256':hashlib.sha256((CACHE/'scene_data.json').read_bytes()).hexdigest(),
        'archived_source_sha256':{str(p.relative_to(source)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(source.rglob('*')) if p.is_file() and '__pycache__' not in p.parts},
        'scope':'Finite exact fixture and contact-atlas checks, not a new global theorem verification.'}
    dump(HERE/'DATA_CHECKS.json',receipt)
    print('PASS: four digests, exact periodic witness, solid overlap section, 1/64/4096 nested patches')

if __name__=='__main__': main()
