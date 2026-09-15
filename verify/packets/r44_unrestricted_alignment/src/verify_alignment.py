#!/usr/bin/env python3
"""Mesh-derived alignment audit for the unchanged R44 solid.

Standard library only. This verifier imports no upstream program. Native
features are extracted from connected components of the non-axis mesh faces;
patch/profile annotations are checked only afterwards, not trusted as inputs.
The continuous lemmas are proved in ALIGNMENT_PROOF.md, not by this program.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
import argparse, gzip, hashlib, json, time

ROOT = Path(__file__).resolve().parents[1]
ZERO = (0, 0, 0)
IDENTITY = (1, 2, 3) # signed images of the three INPUT basis vectors
ETA = F(1, 100)
HEIGHT_UNIT = F(1, 10000)
RHO = F(1, 100)
CELLS = tuple(b for b in product((0, 1), repeat=3) if b != (1, 1, 1))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def add(a, b): return tuple(x+y for x, y in zip(a, b))
def sub(a, b): return tuple(x-y for x, y in zip(a, b))
def mul(s, a): return tuple(s*x for x in a)
def dot(a, b): return sum(x*y for x, y in zip(a, b))
def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])


def apply(g, x):
    # The representation is column based, unlike both upstream programs.
    out = [0, 0, 0]
    for j, v in enumerate(g):
        out[abs(v)-1] += (1 if v > 0 else -1)*x[j]
    return tuple(out)


def inverse(g):
    ans = [0, 0, 0]
    for j, v in enumerate(g):
        ans[abs(v)-1] = (1 if v > 0 else -1)*(j+1)
    return tuple(ans)


def from_upstream_pose(record):
    (perm, signs), shift = record
    g = [0, 0, 0]
    for i, j in enumerate(perm):
        g[j] = signs[i]*(i+1)
    return tuple(g), tuple(shift)


def determinant(g):
    p = [abs(x)-1 for x in g]
    inversions = sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
    return (-1)**inversions * (-1)**sum(x < 0 for x in g)


FRAMES = tuple(sorted(tuple(signs[j]*p[j] for j in range(3))
    for p in permutations((1, 2, 3)) for signs in product((-1, 1), repeat=3)))


def panel_inventory():
    result = {}
    for cell in CELLS:
        for axis in range(3):
            for sign in (-1, 1):
                adjacent = list(cell); adjacent[axis] += sign
                if tuple(adjacent) in CELLS:
                    continue
                center2 = [2*x+1 for x in cell]; center2[axis] += sign
                result[axis, tuple(center2)] = sign
    return tuple(sorted(result.items()))


PANELS = panel_inventory()
OFFSETS8 = ((-1,-2), (-1,2), (1,-2), (1,2),
            (-2,-1), (-2,1), (2,-1), (2,1))


def read_mesh_features(solid):
    """Read features from actual triangles, not the supplied patch list."""
    vertices = [tuple(map(F, p)) for p in solid['vertices']]
    triangles = [tuple(t) for t in solid['triangles']]
    incidence = defaultdict(list)
    normals = []
    axis_face = []
    oriented = Counter()
    for tid, t in enumerate(triangles):
        require(len(set(t)) == 3 and all(0 <= x < len(vertices) for x in t), 'bad triangle')
        normal = cross(sub(vertices[t[1]], vertices[t[0]]), sub(vertices[t[2]], vertices[t[0]]))
        require(any(normal), 'degenerate triangle')
        normals.append(normal)
        axis_face.append(sum(x != 0 for x in normal) == 1)
        for a, b in zip(t, t[1:]+t[:1]):
            incidence[tuple(sorted((a,b)))].append(tid)
            oriented[a,b] += 1
    require(all(len(v) == 2 for v in incidence.values()), 'nonmanifold mesh edge')
    require(all(n == 1 and oriented[b,a] == 1 for (a,b), n in oriented.items()), 'unpaired oriented edge')

    sloping = {i for i in range(len(triangles)) if not axis_face[i]}
    adjacency = defaultdict(set)
    for ids in incidence.values():
        i, j = ids
        if i in sloping and j in sloping:
            adjacency[i].add(j); adjacency[j].add(i)
    groups = []
    unvisited = set(sloping)
    while unvisited:
        todo = [min(unvisited)]; unvisited.remove(todo[0]); group = set(todo)
        for i in todo:
            for j in adjacency[i]:
                if j in unvisited:
                    unvisited.remove(j); group.add(j); todo.append(j)
        groups.append(group)
    require(len(groups) == 192 and all(len(g) == 4 for g in groups), 'unexpected feature components')

    features = {}
    marked_edges = {}
    plane_areas = defaultdict(F)
    for tid, n in enumerate(normals):
        if axis_face[tid]:
            ax = next(i for i,x in enumerate(n) if x)
            plane_areas[ax, vertices[triangles[tid][0]][ax]] += abs(n[ax])/2

    for group in groups:
        vc = Counter(v for tid in group for v in triangles[tid])
        require(len(vc) == 5 and sorted(vc.values()) == [2,2,2,2,4], 'not a square-pyramid fan')
        apex_id = next(v for v,n in vc.items() if n == 4)
        base_ids = tuple(v for v in vc if v != apex_id)
        base = [vertices[v] for v in base_ids]
        axes = [ax for ax in range(3) if len({p[ax] for p in base}) == 1]
        require(len(axes) == 1, 'base is not in a coordinate plane')
        axis = axes[0]; tangent = [j for j in range(3) if j != axis]
        center = tuple(sum(p[j] for p in base)/4 for j in range(3))
        apex = vertices[apex_id]
        require(all(apex[j] == center[j] for j in tangent), 'off-center pyramid apex')
        require({tuple(p[j]-center[j] for j in tangent) for p in base} == set(product((-ETA,ETA), repeat=2)), 'wrong square base')
        normals_to_panel = set()
        for tid in group:
            t = triangles[tid]
            for a,b in zip(t, t[1:]+t[:1]):
                key = tuple(sorted((a,b)))
                kind = 'ridge' if apex_id in key else 'base'
                other = next(x for x in incidence[key] if x != tid)
                if kind == 'base':
                    require(axis_face[other], 'base is not collared by a flat panel')
                    nn = normals[other]
                    require(nn[axis] != 0, 'wrong neighboring base plane')
                    normals_to_panel.add(1 if nn[axis] > 0 else -1)
        require(len(normals_to_panel) == 1, 'inconsistent outward panel normal')
        sign = next(iter(normals_to_panel))
        outward = tuple(sign if i == axis else 0 for i in range(3))
        height = (apex[axis]-center[axis])*sign
        coefficient = height/HEIGHT_UNIT
        require(coefficient.denominator == 1 and 1 <= abs(coefficient) <= 12, 'wrong feature height')
        coefficient = int(coefficient)
        center8q = tuple(8*x for x in center)
        require(all(x.denominator == 1 for x in center8q), 'marker center is not eighth-integral')
        center8 = tuple(int(x) for x in center8q)
        matches = []
        for fi, ((ax,c2),panel_sign) in enumerate(PANELS):
            if ax != axis or panel_sign != sign or center[axis] != F(c2[axis],2):
                continue
            delta = tuple(center8[j]-4*c2[j] for j in tangent)
            if delta in OFFSETS8:
                matches.append((fi, OFFSETS8.index(delta)))
        require(len(matches) == 1, 'ambiguous native role reconstruction')
        fi,j = matches[0]; role = 8*fi+j
        require(role not in features, 'duplicate native feature role')
        features[role] = {'role':role, 'center8':center8, 'normal':outward,
                          'coefficient':coefficient, 'base_ids':base_ids, 'apex_id':apex_id}
        for tid in group:
            t = triangles[tid]
            for a,b in zip(t, t[1:]+t[:1]):
                key = tuple(sorted((a,b))); kind = 'ridge' if apex_id in key else 'base'
                value = (kind, abs(coefficient), (1 if coefficient>0 else -1)*(1 if kind=='base' else -1))
                require(key not in marked_edges or marked_edges[key] == value, 'edge annotation conflict')
                marked_edges[key] = value
    require(set(features) == set(range(192)), 'incomplete mesh-derived role inventory')
    require(len(marked_edges) == 1536, 'incomplete feature edge inventory')

    # Independently classify every actual mesh dihedral, including its side.
    hist = Counter()
    for key, (i,j) in incidence.items():
        n,m = normals[i], normals[j]
        cosine2 = dot(n,m)**2/(dot(n,n)*dot(m,m))
        opposite = next(v for v in triangles[j] if v not in key)
        side = dot(n,sub(vertices[opposite],vertices[key[0]]))
        side_sign = (side>0)-(side<0)
        if key in marked_edges:
            kind,height,expected_sign = marked_edges[key]
            ratio = F(height,100)
            expected_cosine2 = 1/(1+ratio*ratio)**(1 if kind=='base' else 2)
            require(cosine2 == expected_cosine2 and dot(n,m)>0 and side_sign==expected_sign, 'feature angle mismatch')
            length2 = dot(sub(vertices[key[0]],vertices[key[1]]),sub(vertices[key[0]],vertices[key[1]]))
            require(length2 == (4*ETA*ETA if kind=='base' else 2*ETA*ETA+(height*HEIGHT_UNIT)**2), 'feature edge length mismatch')
            hist[kind,height,side_sign] += 1
        else:
            require(cosine2 in (0,1), 'unlisted nonfeature angle')
            if cosine2 == 1:
                require(dot(n,m)>0 and side_sign==0, 'invalid flat edge')
                hist['flat',0,0] += 1
            else:
                require(side_sign in (-1,1), 'invalid carrier edge')
                hist['carrier',0,side_sign] += 1
    for j in range(1,13):
        for kind in ('base','ridge'):
            for sign in (-1,1):
                require(hist[kind,j,sign] == 32, 'wrong angle multiplicity')
    require([features[i]['coefficient'] for i in range(192)] == solid['profile'], 'mesh/profile disagreement')
    patch_lookup = {p['role']:p for p in solid['patches']}
    for role, f in features.items():
        p = patch_lookup[role]
        require(tuple(map(F,p['apex'])) == vertices[f['apex_id']], 'patch/apex disagreement')
        require({tuple(map(F,q)) for q in p['base']} == {vertices[i] for i in f['base_ids']}, 'patch/base disagreement')
        require(p['coefficient'] == f['coefficient'], 'patch/height disagreement')
    return features, {
        'vertices':len(vertices), 'triangles':len(triangles), 'all_edges':len(incidence),
        'sloping_triangles':len(sloping), 'square_pyramids_extracted_without_patch_annotations':len(groups),
        'feature_edges':len(marked_edges), 'unlisted_nonflat_angles':0,
        'angle_histogram':[[*k,v] for k,v in sorted(hist.items())],
        'axis_planes':[[ax,str(z),str(area)] for (ax,z),area in sorted(plane_areas.items())]
    }


def cell_lowers8(g):
    ans = []
    for c in CELLS:
        # Transform all eight corners, rather than using signed rounding.
        corners = [apply(g, add(c,b)) for b in product((0,1),repeat=3)]
        ans.append(tuple(8*min(v[i] for v in corners) for i in range(3)))
    return tuple(ans)


def first_overlap(boxes_a, boxes_b):
    for ia,a in enumerate(boxes_a):
        for ib,b in enumerate(boxes_b):
            lo = tuple(max(a[i],b[i]) for i in range(3))
            hi = tuple(min(a[i]+8,b[i]+8) for i in range(3))
            if all(lo[i]<hi[i] for i in range(3)):
                return ia,ib,lo,hi
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--solid', type=Path, default=ROOT/'input/r44_solid.json')
    parser.add_argument('--collisions', type=Path, default=ROOT/'input/companion_collision_certificate.json')
    parser.add_argument('--registered', type=Path, default=ROOT/'input/candidate_certificate.json')
    parser.add_argument('--output', type=Path, default=ROOT/'results/alignment_verification.json')
    parser.add_argument('--core-witnesses', type=Path, default=None,
                        help='Optionally export one explicit retained-core overlap box per rejected companion option.')
    args = parser.parse_args(); start = time.monotonic()
    solid = json.loads(args.solid.read_text())
    features, mesh_report = read_mesh_features(solid)

    ratios = [F(j,100) for j in range(1,13)]
    require(all(0<t<1 and (1+t*t)**2<2 for t in ratios), 'angle range failed')
    require(all(1+x*x != (1+y*y)**2 for x in ratios for y in ratios), 'base/ridge angle collision')
    L = max(ratios)
    require(8*L*L < 1, 'three-cone exclusion failed')
    require(63*L*L < 1, 'stronger source cone bound failed')
    require(12*HEIGHT_UNIT < RHO and 2*RHO < F(1,8), 'core margin failed')
    for a in features.values():
        for b in features.values():
            if a['role']>=b['role']: continue
            # Distinct features on a common panel have disjoint collars.
            if a['normal']==b['normal']:
                ax=next(i for i,n in enumerate(a['normal']) if n)
                if a['center8'][ax]==b['center8'][ax]:
                    require(max(abs(a['center8'][i]-b['center8'][i]) for i in range(3) if i!=ax) >= 1, 'feature supports insufficiently separated')

    # Derive the mate list from actual mesh features. No registered or hierarchy
    # certificate is used in producing these possibilities.
    mate_roles = defaultdict(set)
    for g in FRAMES:
        moved = [(f['role'], apply(g,f['center8']), apply(g,f['normal']), f['coefficient']) for f in features.values()]
        for u in features.values():
            for _,center,normal,height in moved:
                if normal==mul(-1,u['normal']) and height==-u['coefficient']:
                    mate_roles[g,sub(u['center8'],center)].add(u['role'])
    require(len(mate_roles)==6862, 'raw mate census mismatch')
    native_boxes={g:cell_lowers8(g) for g in FRAMES}
    root_boxes=native_boxes[IDENTITY]
    boxes={pose:tuple(add(c,pose[1]) for c in native_boxes[pose[0]]) for pose in mate_roles}
    direct_overlap={p:first_overlap(root_boxes,b) for p,b in boxes.items()}
    isolated={p for p,overlap in direct_overlap.items() if overlap is None}
    require(len(isolated)==5317, 'isolated mate census mismatch')
    fractional=sum(any(t%8 for t in shift) for _,shift in isolated)
    require(fractional==5234, 'fractional census mismatch')
    partner_options={u:tuple(sorted(p for p in isolated if u in mate_roles[p])) for u in range(192)}
    collision_cert=json.loads(args.collisions.read_text())
    rejected=[from_upstream_pose(w['rejected_pose']) for w in collision_cert['witnesses']]
    require(len(rejected)==len(set(rejected))==5273, 'duplicate/missing rejection witness')
    require(set(rejected)<=isolated, 'rejection outside isolated carrier')

    checks=0;min_core_width=None;counts=Counter();proof_stream=None
    if args.core_witnesses:
        args.core_witnesses.parent.mkdir(parents=True,exist_ok=True)
        proof_stream=gzip.open(args.core_witnesses,'wt',encoding='utf-8')
    try:
        for record,p in zip(collision_cert['witnesses'],rejected):
            owner=record['marker_owner']; role=record['native_role']
            require(owner in (0,1) and role in features, 'bad witness marker')
            if owner:
                g,t=p;gi=inverse(g);p=(gi,mul(-1,apply(gi,t)))
            require(p in isolated, 'inverted pose not isolated')
            options=partner_options[role]
            require(options and p not in options, 'other tile can fill the specified feature')
            require(len(options)==record['possible_partners'], 'incomplete partner quantifier')
            overlaps=[]
            for q in options:
                overlap=first_overlap(boxes[p],boxes[q])
                require(overlap is not None, 'companion has no demonstrated core collision')
                ia,ib,lo,hi=overlap
                # A physical, positive-volume overlap, not merely a baseline hit.
                widths=[F(hi[i]-lo[i],8)-2*RHO for i in range(3)]
                require(min(widths)>=F(21,200), 'insufficient retained-core collision')
                min_core_width=min(widths) if min_core_width is None else min(min_core_width,min(widths))
                checks+=1
                if proof_stream: overlaps.append([list(q[0]),list(q[1]),ia,ib,list(lo),list(hi)])
            counts[len(options)]+=1
            if proof_stream:
                proof_stream.write(json.dumps({'original_pair':record['rejected_pose'], 'marker_owner':owner,
                    'native_role':role,'normalized_other':[p[0],p[1]],'overlaps':overlaps},separators=(',',':'))+'\n')
    finally:
        if proof_stream:proof_stream.close()
    require(checks==299975, 'wrong collision total')
    survivors=isolated-set(rejected)
    require(len(survivors)==44, 'survivor count mismatch')
    require(all(all(t%8==0 for t in shift) for _,shift in survivors), 'fractional survivor')
    require(all(determinant(g)==1 for g,_ in survivors), 'improper survivor')
    # Only now connect to the previously verified registered theorem.
    registered=json.loads(args.registered.read_text())
    registered44={from_upstream_pose(p) for p in registered['legal_contacts']}
    integral44={(g,tuple(t//8 for t in shift)) for g,shift in survivors}
    require(integral44==registered44, 'survivors not identical to registered 44 atlas')

    # Recheck the whole-panel physical matching of every survivor directly.
    root_index={(f['center8'],f['normal']):f['coefficient'] for f in features.values()}
    for g,shift in survivors:
        moved={(add(apply(g,f['center8']),shift),apply(g,f['normal'])):f['coefficient'] for f in features.values()}
        for (c,n),height in root_index.items():
            mate=moved.get((c,mul(-1,n)))
            if mate is not None:require(mate==-height, 'surviving feature sign conflict')

    report={
        'status':'PASS','unchanged_solid_sha256':hashlib.sha256(args.solid.read_bytes()).hexdigest(),
        'mesh_derived':mesh_report,
        'analytic_constants':{'base_halfwidth':str(ETA),'height_unit':str(HEIGHT_UNIT),'maximum_graph_slope':str(L),
             '8_L_squared':str(8*L*L),'63_L_squared':str(63*L*L),
             'three_feature_tangent_cones_cannot_coexist':True,'pairwise_distinct_angle_deviations':24,
             'retained_core_margin':str(RHO),'minimum_demonstrated_core_overlap_width':str(min_core_width),
             'each_collision_contains_an_open_ball_of_radius_at_least':str(F(21,400))},
        'complete_feature_mates':{'raw':len(mate_roles),'directly_core_colliding':len(mate_roles)-len(isolated),
             'isolated':len(isolated),'fractional_isolated':fractional,'integral_isolated':len(isolated)-fractional,
             'rejected_with_exhaustive_companion_collision':len(rejected),'companion_options_checked':checks,
             'survivors':len(survivors),'fractional_survivors':0,'improper_survivors':0,
             'same_as_registered_atlas_as_sets':True,'option_count_histogram':sorted(counts.items())},
        'independence':{'imports_upstream_programs':False,'imports_third_party_packages':False,
             'feature_geometry_taken_from_actual_triangles':True,'uses_flat_panel_filter_to_reject_placements':False,
             'uses_existing_rejections_to_prune_companion_options':False,
             'geometric_lemmas_proof_assistant_formalized':False,'external_review':False},
        'inputs':{str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in (args.solid,args.collisions,args.registered)},
        'seconds':time.monotonic()-start}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
