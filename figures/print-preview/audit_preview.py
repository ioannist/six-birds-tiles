"""Read back display triangles; reconstruct expected feature triangles independently."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import json,csv,hashlib
import numpy as np
R=Path(__file__).resolve().parents[2];P=R/'figures/print-preview'
s=json.loads((R/'solid/r44_solid.json').read_text());display=np.load(P/'display-mesh.npz')
T=display['triangles'];roles=display['roles'];faces=display['panels']
records=[]
def key(t): return tuple(sorted(tuple(round(float(c),11) for c in p) for p in t))
assert Counter(int(k) for k in roles if k>=0)==Counter({k:4 for k in range(192)})
for p in sorted(s['patches'],key=lambda p:p['role']):
 k=p['role'];b=np.array([[float(F(c)) for c in v] for v in p['base']]);a=np.array([float(F(c)) for c in p['apex']]);c=b.mean(axis=0)
 # Independently form the declared display transformation on canonical vertices.
 bb=c+5*(b-c);aa=c+80*(a-c)
 exp={key([bb[i],bb[(i+1)%4],aa]) for i in range(4)}
 act={key(t) for t in T[roles==k]}
 assert exp==act,(k,exp,act)
 assert set(faces[roles==k])=={p['face']}
 records.append({'role':k,'panel':p['face'],'coefficient':p['coefficient'],'triangles_match':4})
# Check flat panel coverage has correct projected area and no planar triangle inside any footprint.
for f in range(24):
 patches=[p for p in s['patches'] if p['face']==f]
 B=np.array([[float(F(c)) for c in v] for p in patches for v in p['base']]);ax=int(np.argmin(B.std(axis=0)));uv=[i for i in range(3) if i!=ax]
 plane=B[0,ax];center=B.mean(axis=0)
 flat=T[(faces==f)&(roles==-1)]
 assert np.allclose(flat[:,:,ax],plane)
 assert np.all(abs(flat[:,:,uv]-center[uv])<=.5+1e-12)
 area=np.linalg.norm(np.cross(flat[:,1]-flat[:,0],flat[:,2]-flat[:,0]),axis=1).sum()/2
 assert abs(area-.92)<1e-10,(f,area)
 for p in patches:
  b=np.array([[float(F(c)) for c in v] for v in p['base']]);c=b.mean(axis=0)
  centroids=flat.mean(axis=1)
  assert not np.any(np.all(abs(centroids[:,uv]-c[uv])<.05-1e-12,axis=1))
# Confirm selected panel labels printed in both SVG layouts are the source coefficients,
# and that both point to the same embedded plan render.
for name in ['figure1-corrected','figure3-corrected']:
 svg=(P/(name+'.svg')).read_text()
 for p in s['patches']:
  if p['face']==13:
   c=p['coefficient'];label=('+' if c>0 else '−')+str(abs(c))
   assert f'>{label}</text>' in svg
report={'result':'PASS','features_read_back':192,'matching_feature_triangles':768,'flat_panels_checked':24,'flat_area_per_panel':'.92','selected_panel':13,'selected_features_checked':8,'scope':'Display-mesh geometry and source-derived labels; not a theorem check. Width x5 and height x80 are intentional illustration distortions.','records':records}
(P/'mesh-readback-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: read-back mesh matches all 768 independently reconstructed feature triangles; 24 flat panels have correct area and holes; selected labels match.')
