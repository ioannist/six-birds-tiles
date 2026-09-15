"""Standalone artwork construction; never edits theorem, canonical data or paper sources."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import json,csv,hashlib,sys,importlib.util,io,base64
import numpy as np
from PIL import Image
import cairosvg
ROOT=Path(__file__).resolve().parents[2]; OUT=ROOT/'figures/print-preview'
spec=importlib.util.spec_from_file_location('r44render',ROOT/'figures/render_r44.py')
r=importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
s=json.loads((ROOT/'solid/r44_solid.json').read_text())
rows=list(csv.DictReader((ROOT/'solid/native_panels.csv').open()))
eta=F(s['base_halfwidth']); hu=F(s['height_unit']); WIDTH=F(5); HEIGHT=F(80)
MARKS=[(-1,-2),(-1,2),(1,-2),(1,2),(-2,-1),(-2,1),(2,-1),(2,1)]
SELECT=13
# All data checks use rational arithmetic, before conversion for display.
V=[tuple(map(F,p)) for p in s['vertices']]; VI={p:i for i,p in enumerate(V)}
meshfaces={frozenset(t) for t in s['triangles']}
features={}; panels={}; checks=[]
cells={tuple(c) for c in s['base_unit_cubes']}
exposed=set()
for c in cells:
 for ax in range(3):
  for sg in [-1,1]:
   nb=list(c);nb[ax]+=sg
   if tuple(nb) in cells:continue
   cc=[F(x)+F(1,2) for x in c];cc[ax]+=F(sg,2)
   exposed.add((ax,sg,tuple(cc)))
assert len(exposed)==24
for row in rows:
 f=int(row['panel']);ax=int(row['normal_axis']);sg=int(row['outward_sign'])
 pc=tuple(F(row['center_'+a]) for a in 'xyz');n=tuple(F(sg if a==ax else 0) for a in range(3))
 assert (ax,sg,pc) in exposed
 panels[f]={'axis':ax,'sign':sg,'centre':pc,'normal':n,'uv':[a for a in range(3) if a!=ax]}
assert len(panels)==24
for p in s['patches']:
 role=p['role'];f=p['face'];k=role%8;assert role//8==f and role not in features
 pn=panels[f];u,v=pn['uv'];n=pn['normal'];pc=pn['centre']
 B=[tuple(map(F,q)) for q in p['base']];A=tuple(map(F,p['apex']))
 C=tuple(sum(b[a] for b in B)/4 for a in range(3))
 expected=list(pc);expected[u]+=F(MARKS[k][0],8);expected[v]+=F(MARKS[k][1],8)
 assert C==tuple(expected)
 coef=int(p['coefficient']); assert coef==s['profile'][role]==int(rows[f]['a_'+str(k)])
 assert A==tuple(C[a]+coef*hu*n[a] for a in range(3))
 assert set(B)=={tuple(C[a]+(du*eta if a==u else dv*eta if a==v else 0) for a in range(3)) for du in [-1,1] for dv in [-1,1]}
 assert all(b in VI for b in B) and A in VI
 assert all(frozenset((VI[B[j]],VI[B[(j+1)%4]],VI[A])) in meshfaces for j in range(4))
 DB=[tuple(C[a]+WIDTH*(b[a]-C[a]) for a in range(3)) for b in B]
 DA=tuple(C[a]+HEIGHT*(A[a]-C[a]) for a in range(3))
 assert tuple(sum(b[a] for b in DB)/4 for a in range(3))==C
 assert tuple((DA[a]-C[a])/HEIGHT for a in range(3))==tuple(A[a]-C[a] for a in range(3))
 assert all(abs(b[a]-pc[a])<F(1,2) for b in DB for a in [u,v])
 features[role]={'role':role,'face':f,'k':k,'coef':coef,'centre':C,'base':DB,'apex':DA,'true_base':B,'true_apex':A}
 checks.append({'role':role,'panel':f,'local_index':k,'centre_x':str(C[0]),'centre_y':str(C[1]),'centre_z':str(C[2]),'signed_coefficient':coef,'signed_true_height':str(coef*hu),'display_width_factor':str(WIDTH),'display_height_factor':str(HEIGHT),'canonical_mesh_faces':'4/4','panel_table':'PASS','profile':'PASS','display_centre_sign_height':'PASS'})
assert set(features)==set(range(192))
assert Counter(p['face'] for p in features.values())==Counter({f:8 for f in range(24)})
for f,pn in panels.items():
 fs=[p for p in features.values() if p['face']==f];u,v=pn['uv']
 for i,p in enumerate(fs):
  for q in fs[i+1:]:
   assert abs(p['centre'][u]-q['centre'][u])>=2*WIDTH*eta or abs(p['centre'][v]-q['centre'][v])>=2*WIDTH*eta
with (OUT/'feature-audit.csv').open('w') as fh:
 w=csv.DictWriter(fh,fieldnames=checks[0].keys());w.writeheader();w.writerows(sorted(checks,key=lambda x:x['role']))
print('Exact checks PASS: 192/192 features; 24 panels x 8; all 768 canonical feature triangles.',flush=True)

# Build the flat panel minus eight footprint holes, then four faces for each pyramid.
# Polygons are oriented with the canonical outward normal. There is no flat face covering a dent.
tri=[];tri_role=[];tri_panel=[];edge_by_role={};boundary=[];corner_by_panel={}
def add_triangle(q,n,role,f):
 a=np.array(q,float);nn=np.cross(a[1]-a[0],a[2]-a[0])
 if np.dot(nn,np.array(n,float))<0:a=a[[0,2,1]]
 tri.append(a);tri_role.append(role);tri_panel.append(f)
for f,pn in panels.items():
 u,v=pn['uv'];C=pn['centre'];n=pn['normal'];fs=[features[8*f+k] for k in range(8)]
 def pt(uu,vv):
  a=list(C);a[u]=uu;a[v]=vv;return tuple(a)
 bounds=[(min(b[u] for b in p['base']),max(b[u] for b in p['base']),min(b[v] for b in p['base']),max(b[v] for b in p['base'])) for p in fs]
 us=sorted({C[u]-F(1,2),C[u]+F(1,2)}|{x for bb in bounds for x in bb[:2]})
 vs=sorted({C[v]-F(1,2),C[v]+F(1,2)}|{x for bb in bounds for x in bb[2:]})
 area=F(0)
 for a0,a1 in zip(us,us[1:]):
  for b0,b1 in zip(vs,vs[1:]):
   ac=(a0+a1)/2;bc=(b0+b1)/2
   if any(lo<ac<hi and bot<bc<top for lo,hi,bot,top in bounds):continue
   q=[pt(a0,b0),pt(a1,b0),pt(a1,b1),pt(a0,b1)]
   add_triangle(q[:3],n,-1,f);add_triangle([q[0],q[2],q[3]],n,-1,f)
   area+=(a1-a0)*(b1-b0)
 assert area+8*(2*WIDTH*eta)**2==1
 Q=[pt(C[u]+du,C[v]+dv) for du,dv in [(-F(1,2),-F(1,2)),(F(1,2),-F(1,2)),(F(1,2),F(1,2)),(-F(1,2),F(1,2))]]
 corner_by_panel[f]=np.array(Q,float)
 boundary.extend([(Q[j],Q[(j+1)%4]) for j in range(4)])
 for p in fs:
  B=p['base'];A=p['apex'];role=p['role']
  edge_by_role[role]=[(B[j],B[(j+1)%4]) for j in range(4)]+[(B[j],A) for j in range(4)]
  for j in range(4):add_triangle([B[j],B[(j+1)%4],A],n,role,f)
tri=np.array(tri);tri_role=np.array(tri_role);tri_panel=np.array(tri_panel)
np.savez_compressed(OUT/'display-mesh.npz',triangles=tri,roles=tri_role,panels=tri_panel)
assert Counter(int(i) for i in tri_role if i>=0)==Counter({k:4 for k in range(192)})

class Ortho:
 def __init__(self,eye_direction,target,scale,w,h,up=(0,0,1)):
  n=np.array(eye_direction,float);n/=np.linalg.norm(n);self.n=n
  right=np.cross(-n,np.array(up,float));right/=np.linalg.norm(right);up=np.cross(right,-n)
  self.basis=np.array([right,up,-n]);self.target=np.array(target);self.scale=scale;self.w=w;self.h=h
 def project(self,pts):
  x=(np.asarray(pts)-self.target)@self.basis.T
  return np.column_stack([self.w/2+x[:,0]*self.scale,self.h/2-x[:,1]*self.scale]),10+x[:,2]

def render(which,cam,filename):
 ids=np.arange(len(tri)) if which is None else np.where(tri_panel==which)[0]
 T=tri[ids];roles=tri_role[ids]
 N=np.cross(T[:,1]-T[:,0],T[:,2]-T[:,0]);N/=np.linalg.norm(N,axis=1)[:,None]
 # One fixed world-space lamp; no arbitrary reassignment of polarity or facet type.
 light=np.array([-0.5,-0.9,1.6]);light/=np.linalg.norm(light)
 shades=0.86+0.12*np.maximum(0,N@light)
 # Darker annotation for recesses, supplemented by signed coefficients in the detail.
 for i,role in enumerate(roles):
  if role>=0:
   shades[i]=0.32+0.63*max(0,float(N[i]@light))
 img=np.ones((cam.h,cam.w,3));z=np.full((cam.h,cam.w),np.inf)
 r.rasterize(T,np.repeat(shades[:,None],3,axis=1),cam,z,img)
 edges=[]
 for k,segs in edge_by_role.items():
  if which is None or features[k]['face']==which:edges.extend(segs)
 r.draw_edges(np.array(edges,float),cam,z,img,np.array([.10]*3),1.5,bias=0.00035)
 B=boundary if which is None else [(corner_by_panel[which][i],corner_by_panel[which][(i+1)%4]) for i in range(4)]
 r.draw_edges(np.array(B,float),cam,z,img,np.array([.26]*3),2.0,bias=0.00015)
 Image.fromarray(np.round(img*255).astype('uint8')).save(filename)
 # Actual per-feature projected visibility, using final z-buffer at all triangle sample pixels.
 # Positive means the feature really contributes to this view rather than being hidden.
 visible={}
 for role in (range(192) if which is None else range(which*8,which*8+8)):
  TT=tri[tri_role==role];ss,dd=cam.project(TT.reshape(-1,3));ss=ss.reshape(-1,3,2);dd=dd.reshape(-1,3)
  count=0
  for pp,zz in zip(ss,dd):
   x0=max(0,int(np.floor(pp[:,0].min())));x1=min(cam.w-1,int(np.ceil(pp[:,0].max())))
   y0=max(0,int(np.floor(pp[:,1].min())));y1=min(cam.h-1,int(np.ceil(pp[:,1].max())))
   if x1<x0 or y1<y0:continue
   X,Y=np.meshgrid(np.arange(x0,x1+1)+.5,np.arange(y0,y1+1)+.5)
   (ax,ay),(bx,by),(cx,cy)=pp;ar=(bx-ax)*(cy-ay)-(by-ay)*(cx-ax)
   if abs(ar)<1e-12:continue
   w0=((bx-X)*(cy-Y)-(by-Y)*(cx-X))/ar;w1=((cx-X)*(ay-Y)-(cy-Y)*(ax-X))/ar;w2=1-w0-w1
   dep=w0*zz[0]+w1*zz[1]+w2*zz[2]
   count+=int(((w0>=0)&(w1>=0)&(w2>=0)&(abs(dep-z[y0:y1+1,x0:x1+1])<1e-7)).sum())
  visible[role]=count
 return visible

cam=Ortho((5.2,-6.4,3.65),(1,1,1),540,1740,1620)
visibility=render(None,cam,OUT/'chair-render.png')
pn=panels[SELECT];C=np.array(pn['centre'],float)
insetcam=Ortho((0,-1,0),C,980,1100,1100)
insetvis=render(SELECT,insetcam,OUT/'panel-plan-render.png')
obcam=Ortho((.25,-1,.7),C,990,1250,1160)
obvis=render(SELECT,obcam,OUT/'panel-oblique-render.png')
assert all(visibility[k]>50 and insetvis[k]>50 and obvis[k]>50 for k in range(8*SELECT,8*SELECT+8))
with (OUT/'visibility-audit.csv').open('w') as fh:
 w=csv.writer(fh);w.writerow(['role','panel','chair_visible_pixels','inset_visible_pixels','panel_oblique_visible_pixels'])
 for k in range(192):w.writerow([k,k//8,visibility[k],insetvis.get(k,''),obvis.get(k,'')])
print('Highlighted panel 13: all 8 features visible in chair, inset and oblique view.',flush=True)

# SVG layout: embedded deterministic geometry, vector text/leader lines.
def text(x,y,t,size=24,anchor='start',weight='normal'):
 return f'<text x="{x:.2f}" y="{y:.2f}" text-anchor="{anchor}" font-family="DejaVu Sans,sans-serif" font-size="{size}" font-weight="{weight}" fill="#181818">{t}</text>'
def line(points,width=1.6,color='#333',dash=''):
 pts=' '.join(f'{x:.2f},{y:.2f}' for x,y in points)
 return f'<polyline points="{pts}" fill="none" stroke="{color}" stroke-width="{width}"'+(f' stroke-dasharray="{dash}"' if dash else '')+'/>'
def embedded(path,x,y,w,h):
 data=base64.b64encode(path.read_bytes()).decode()
 return f'<image x="{x}" y="{y}" width="{w}" height="{h}" href="data:image/png;base64,{data}"/>'
def doc(w,h,parts):return f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}"><rect width="100%" height="100%" fill="white"/>'+''.join(parts)+'</svg>'
def save(name,w,h,parts):
 svg=doc(w,h,parts);(OUT/(name+'.svg')).write_text(svg)
 cairosvg.svg2png(bytestring=svg.encode(),write_to=str(OUT/(name+'.png')),output_width=w*2,output_height=h*2)
 cairosvg.svg2pdf(bytestring=svg.encode(),write_to=str(OUT/(name+'.pdf')))
def coef(c):return ('+' if c>0 else '−')+str(abs(c))
def signs(camera,dx,dy,scale,font):
 out=[];pn=panels[SELECT];C=np.array(pn['centre'],float)
 for k in range(8*SELECT,8*SELECT+8):
  p=features[k];cen=np.array(p['centre'],float)
  # Place each annotation radially away from feature group; never modify the centre.
  mark=C+(cen-C)*1.60
  xy,_=camera.project(mark[None,:]);xx,yy=xy[0]*scale+[dx,dy]
  out.append(text(xx,yy+font*.34,coef(p['coef']),font,'middle'))
 return out
# Figure 1: overall solid, numbered selected panel, exact matching plan inset.
parts=[text(42,48,'Q — seven-cube chair',31,weight='bold'),text(1000,48,'Panel 13 · eight features',29,weight='bold')]
parts.append(embedded(OUT/'chair-render.png',0,75,980,912.414))
parts.append(embedded(OUT/'panel-plan-render.png',995,94,590,590))
parts+=signs(insetcam,995,94,590/1100,24)
# Keep the camera orientation: x to right and z up in the inset, no mirroring.
parts+=[text(1290,685,'x →',22,'middle'),text(994,165,'z ↑',22,'end')]
box=corner_by_panel[SELECT];xy,_=cam.project(box);xy=xy*(980/1740)+[0,75]
parts.append(line(list(xy)+[xy[0]],3.0,'#000'))
pc,_=cam.project(np.array(pn['centre'],float)[None,:]);px,py=pc[0]*(980/1740)+[0,75]
parts.append(text(px,py+7,'13',24,'middle','bold'))
right=xy[np.argmax(xy[:,0])]
parts.append(line([right,[975,right[1]],[1027.18,389]],1.8,'#555'))
parts+=[text(1030,752,'Protrusion (+)',23),text(1352,752,'Recess (−)',23)]
# Actual two local features, separated cross sections with shared exaggeration.
for role,x0 in [(108,1025),(104,1320)]:
 p=features[role];h=float(p['coef']*hu*HEIGHT);span=200;baseline=835;sc=850
 xx=x0+span/2;ee=float(WIDTH*eta)*sc;apex=baseline-h*sc
 points=[(x0,baseline),(xx-ee,baseline),(xx,apex),(xx+ee,baseline),(x0+span,baseline)]
 poly=points+[(x0+span,915),(x0,915)]
 parts.append('<polygon points="'+' '.join(f'{x},{y}' for x,y in poly)+'" fill="#ededed"/>')
 parts.append(line([(x0,baseline),(x0+span,baseline)],1,'#aaa','5 5'))
 parts.append(line(points,2.5))
 parts.append(text(xx,946,f'a = {coef(p["coef"])}',22,'middle'))
parts+=[text(42,1037,'Exact feature centres and signed height ratios · bases ×5 · heights ×80',23),text(42,1073,'Relief exaggerated for visibility; the carrier retains its true proportions.',22)]
save('figure1-corrected',1630,1100,parts)

# Figure 3: larger oblique view and exact plan, of the SAME panel 13.
parts=[text(42,48,'One exposed panel · panel 13',31,weight='bold'),text(930,48,'Exact arrangement',28,weight='bold')]
parts.append(embedded(OUT/'panel-oblique-render.png',0,70,890,825.92))
parts+=signs(obcam,0,70,890/1250,25)
parts.append(embedded(OUT/'panel-plan-render.png',950,100,570,570))
parts+=signs(insetcam,950,100,570/1100,24)
parts+=[text(1235,680,'x →',22,'middle'),text(945,400,'z ↑',22,'end'),text(1040,735,'+ protrusion    − recess',24),text(1040,781,'Signed height: a / 10000',24),text(1040,825,'True base side: 1/50',24),text(42,945,'Same eight features as the highlighted panel in Figure 1.',24),text(42,987,'Centres unchanged · bases ×5 · heights ×80 · signed height ratios preserved',23)]
save('figure3-corrected',1580,1020,parts)
# All 24 panels, in tangent-coordinate views, with signed coefficients and role IDs.
parts=[text(30,42,'All 192 features · panel-by-panel audit',31,weight='bold'),text(30,76,'Panel coordinates use the two remaining global axes in increasing order. Numbers are signed coefficients a.',21)]
for f,pn in panels.items():
 ox=25+(f%4)*395;oy=110+(f//4)*375;sz=310;u,v=pn['uv']
 parts.append(text(ox,oy+22,f'Panel {f}   normal {"+" if pn["sign"]>0 else "−"}{"xyz"[pn["axis"]]}',22,weight='bold'))
 parts.append(f'<rect x="{ox+25}" y="{oy+40}" width="{sz}" height="{sz}" fill="none" stroke="#999"/>')
 parts.append(text(ox+25+sz/2,oy+40+sz/2+7,str(f),24,'middle'))
 for k in range(8):
  p=features[8*f+k];du=float(p['centre'][u]-pn['centre'][u]);dv=float(p['centre'][v]-pn['centre'][v])
  x=ox+25+sz*(.5+du);y=oy+40+sz*(.5-dv)
  parts.append(text(x,y+7,coef(p['coef']),21,'middle'))
  parts.append(text(x,y+22,str(p['role']),11,'middle'))
 parts.append(text(ox+345,oy+350,'xyz'[u]+' →',16))
save('all-panels-audit',1610,2380,parts)
report={'canonical_sha256':hashlib.sha256((ROOT/'solid/r44_solid.json').read_bytes()).hexdigest(),'panel_table_sha256':hashlib.sha256((ROOT/'solid/native_panels.csv').read_bytes()).hexdigest(),'features_checked':192,'panels_checked':24,'canonical_feature_triangles_checked':768,'rendered_feature_triangles':int((tri_role>=0).sum()),'width_factor':str(WIDTH),'height_factor':str(HEIGHT),'selected_panel':SELECT,'selected_roles':list(range(8*SELECT,8*SELECT+8)),'checks':'PASS','source_features':[{'role':k,'panel':p['face'],'coefficient':p['coef'],'centre':[str(x) for x in p['centre']],'base':[[str(x) for x in b] for b in p['true_base']],'apex':[str(x) for x in p['true_apex']],'display_base':[[str(x) for x in b] for b in p['base']],'display_apex':[str(x) for x in p['apex']]} for k,p in sorted(features.items())]}
(OUT/'geometry-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print('Artwork and audit written to',OUT,flush=True)
