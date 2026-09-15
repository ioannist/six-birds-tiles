"""Headless Blender shots. All settled tile poses come from the checked export.

Run through render.py. Blender-only; no UI operations or downloads.
"""
import argparse
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import sys
import time
import bpy
from bpy_extras.object_utils import world_to_camera_view
from mathutils import Matrix, Vector

HERE=Path(__file__).resolve().parent
D=json.loads((HERE/'.cache/scene_data.json').read_text())
SOLID=json.loads((HERE/'.cache/source/solid/r44_solid.json').read_text())
PALETTE=[(0.72,.60,.42,1),(.24,.48,.60,1),(.62,.25,.17,1),(.30,.48,.41,1),(.48,.39,.59,1),(.78,.55,.20,1),(.38,.58,.64,1),(.73,.72,.62,1)]
IVORY=(.72,.69,.60,1)

def smooth(x):
    x=max(0,min(1,x)); return x*x*(3-2*x)
def mix(a,b,t): return a+(b-a)*t
def mesh(name,verts,faces):
    m=bpy.data.meshes.new(name); m.from_pydata(verts,[],faces); m.update(); return m
def material(name,color,metallic=.15):
    m=bpy.data.materials.new(name); m.diffuse_color=color; m.use_nodes=True
    bs=m.node_tree.nodes.get('Principled BSDF'); bs.inputs['Base Color'].default_value=color
    bs.inputs['Roughness'].default_value=.34; bs.inputs['Metallic'].default_value=metallic
    return m
def object_(name,m,mat):
    o=bpy.data.objects.new(name,m); bpy.context.collection.objects.link(o)
    if not m.materials: m.materials.append(mat)
    o.material_slots[0].link='OBJECT'; o.material_slots[0].material=mat
    return o
def pose_matrix(p,scale=1):
    (perm,sign),tr=p
    m=Matrix.Identity(4)
    for i in range(3):
        for j in range(3): m[i][j]=scale*sign[i] if j==perm[i] else 0
        m[i][3]=scale*tr[i]
    return m
def look(o,target): o.rotation_euler=(Vector(target)-o.location).to_track_quat('-Z','Y').to_euler()
def line(name,points,radius,mat):
    c=bpy.data.curves.new(name,'CURVE'); c.dimensions='3D'; c.bevel_depth=radius; c.bevel_resolution=1
    s=c.splines.new('POLY'); s.points.add(len(points)-1)
    for p,v in zip(s.points,points): p.co=(*v,1)
    o=bpy.data.objects.new(name,c); bpy.context.collection.objects.link(o); c.materials.append(mat); return o
def outline(name,p,scale,mat,width=.009):
    # Carrier edges are explanatory outlines, never substituted for Q's mesh.
    M=pose_matrix(p,scale); edges=set()
    for face in D['plain_faces']:
        for a,b in zip(face,face[1:]+face[:1]):
            va=tuple(D['plain_vertices'][a]); vb=tuple(D['plain_vertices'][b])
            edges.add(tuple(sorted((va,vb))))
    objects=[]
    for i,(a,b) in enumerate(sorted(edges)):
        objects.append(line(name+str(i),[M@Vector(a),M@Vector(b)],width,mat))
    return objects

class Studio:
    def __init__(self,shot,width,samples,transparent=False,feature_map=False):
        bpy.ops.wm.read_factory_settings(use_empty=True)
        self.shot=shot; self.scene=bpy.context.scene
        s=self.scene; s.render.engine='CYCLES'; s.cycles.device='GPU'
        pref=bpy.context.preferences.addons['cycles'].preferences
        pref.compute_device_type='OPTIX'; pref.get_devices()
        for dev in pref.devices: dev.use=(dev.type=='OPTIX')
        s.cycles.samples=samples; s.cycles.use_denoising=True
        s.cycles.max_bounces=4; s.cycles.diffuse_bounces=2; s.cycles.glossy_bounces=2
        s.cycles.transparent_max_bounces=4; s.cycles.use_adaptive_sampling=True
        s.cycles.adaptive_threshold=.06; s.cycles.seed=44
        if os.environ.get('R44_VIDEO_ENGINE','EEVEE')=='EEVEE':
            s.render.engine='BLENDER_EEVEE_NEXT'; s.eevee.taa_render_samples=64 if width>=1920 else 16
        s.render.use_persistent_data=True
        s.render.resolution_x=width; s.render.resolution_y=width*9//16; s.render.resolution_percentage=100
        s.render.image_settings.file_format='PNG'; s.render.image_settings.color_mode='RGBA' if transparent else 'RGB'; s.render.image_settings.color_depth='8'
        s.render.film_transparent=transparent; s.render.threads_mode='FIXED'; s.render.threads=12
        s.world=bpy.data.worlds.new('Ink studio'); s.world.use_nodes=True
        s.world.node_tree.nodes['Background'].inputs[0].default_value=(.025,.045,.075,1)
        s.world.node_tree.nodes['Background'].inputs[1].default_value=.35
        s.view_settings.view_transform='AgX'; s.view_settings.look='AgX - Medium High Contrast'
        self.mats=[material('Copy '+str(i),c) for i,c in enumerate(PALETTE)]
        self.ivory=material('Unmarked ivory',IVORY)
        self.ghosts=[]
        for i,m in enumerate(self.mats):
            g=m.copy(); g.name='Transit illustration '+str(i)
            nt=g.node_tree; bs=nt.nodes.get('Principled BSDF'); output=nt.nodes.get('Material Output')
            transparent=nt.nodes.new('ShaderNodeBsdfTransparent'); mixnode=nt.nodes.new('ShaderNodeMixShader')
            mixnode.inputs[0].default_value=.38
            nt.links.new(transparent.outputs[0],mixnode.inputs[1]); nt.links.new(bs.outputs[0],mixnode.inputs[2]); nt.links.new(mixnode.outputs[0],output.inputs['Surface'])
            self.ghosts.append(g)
        self.gold=material('Annotation gold',(.95,.56,.10,1),.4)
        self.coral=material('Annotation coral',(.75,.15,.08,1))
        self.blue=material('Annotation blue',(.1,.48,.74,1))
        self.q=mesh('Q canonical: 2138 vertices / 4272 triangles',D['vertices'],D['triangles'])
        self.plain=mesh('Plain carrier boundary',D['plain_vertices'],D['plain_faces'])
        camera=bpy.data.cameras.new('Camera'); self.cam=bpy.data.objects.new('Camera',camera); bpy.context.collection.objects.link(self.cam)
        camera.type='ORTHO'; camera.lens=50; camera.clip_start=.001; camera.clip_end=2000; s.camera=self.cam
        self.lights=[]
        for name,pos,power,size,color in [('Key',(-3,0,7),1500,5,(1,.86,.68)),('Cool rim',(3,4,5),2100,4,(.55,.75,1)),('Fill',(1,-4,2),500,4,(.75,.86,1))]:
            d=bpy.data.lights.new(name,'AREA'); d.energy=power; d.shape='DISK'; d.size=size; d.color=color
            o=bpy.data.objects.new(name,d); bpy.context.collection.objects.link(o); o.location=pos; self.lights.append((o,Vector(pos),power,size))
        floor=mesh('Stage',[(-500,-500,0),(500,-500,0),(500,500,0),(-500,500,0)],[(0,1,2,3)])
        self.floor=object_('Stage',floor,material('Midnight',(.009,.016,.028,1),.1)); self.floor.location.z=-.045
        self.objects=[]; self.extra=[]
        self.monocolor=False
        self.setup()
        if transparent:
            self.floor.hide_render=True
        if feature_map:
            self.add_feature_map()
        if feature_map and transparent:
            # Keep audit glyphs legible on faces turned away from the studio
            # lights. Emission affects only this annotated display layer.
            for mat in [self.ivory,self.coral,self.blue]:
                bs=mat.node_tree.nodes.get('Principled BSDF')
                if 'Emission Color' in bs.inputs:
                    bs.inputs['Emission Color'].default_value=mat.diffuse_color
                    bs.inputs['Emission Strength'].default_value=.35

    def add_feature_map(self):
        """Add flat, enlarged polarity glyphs over Q; these are annotations."""
        for patch in SOLID['patches']:
            base=[Vector(tuple(float(Fraction(c)) for c in vertex)) for vertex in patch['base']]
            apex=Vector(tuple(float(Fraction(c)) for c in patch['apex']))
            centre=sum(base,Vector())/4
            delta=apex-centre
            outward=delta.normalized() if patch['coefficient']>0 else -delta.normalized()
            outer=[centre+(vertex-centre)*5+outward*.004 for vertex in base]
            if patch['coefficient']>0:
                marker=mesh('Feature-map bump '+str(patch['role']),outer,[(0,1,2,3)])
                self.extra.append(object_('Feature-map bump '+str(patch['role']),marker,self.coral))
            else:
                inner=[centre+(vertex-centre)*2.7+outward*.005 for vertex in base]
                faces=[(i,(i+1)%4,(i+1)%4+4,i+4) for i in range(4)]
                marker=mesh('Feature-map dent '+str(patch['role']),outer+inner,faces)
                self.extra.append(object_('Feature-map dent '+str(patch['role']),marker,self.blue))

    def light_scale(self,center,scale,floor):
        for o,pos,power,size in self.lights:
            o.location=Vector(center)+pos*scale; o.data.energy=power*scale*scale; o.data.size=size*scale; look(o,center)
        self.floor.location.z=floor
    def camera(self,center,span,angle=.8,elevation=.63):
        center=Vector(center)
        self.cam.location=center+Vector((math.cos(angle)*math.cos(elevation),math.sin(angle)*math.cos(elevation),math.sin(elevation)))*span*3
        self.cam.data.ortho_scale=span
        look(self.cam,center)
    def copies(self,poses,plain=False,colors=True,scale=1):
        out=[]
        for i,p in enumerate(poses):
            o=object_('Copy %04d'%i,self.plain if plain else self.q,self.mats[i%8] if colors else self.ivory)
            o.matrix_world=pose_matrix(p,scale); out.append(o)
        return out
    def setup(self):
        shot=self.shot
        if shot in ('hero','outro','plain_hero'):
            self.objects=self.copies(D['sigma'][0],plain=shot=='plain_hero',colors=False); self.light_scale((1,1,1),1,-.045)
        elif shot=='opening_patch':
            self.objects=self.copies(D['sigma'][2]); self.light_scale((4,4,3),4,-.06)
        elif shot in ('macro','macro_restore'):
            # Uniform scale 100 around selected canonical feature. Preserve all aspect ratios.
            center=(2,.25,.375); factor=100
            self.macro_vertices=[tuple((v[i]-center[i])*factor for i in range(3)) for v in D['vertices']]
            self.macro_flat=[tuple((v[i]-center[i])*factor for i in range(3)) for v in D['flat_vertices']]
            m=mesh('Q true geometry uniformly magnified',self.macro_vertices,D['triangles'])
            self.objects=[object_('Magnified Q',m,self.ivory)]
            # Camera and key look along outward +x face, grazing enough to reveal relief.
            self.floor.hide_render=True
            for (o,_,_,_),(pos,power,size) in zip(self.lights,[((.65,-5,2),1600,1.5),((4,3,3),90,3),((2,-3,1),30,2)]):
                o.location=pos; o.data.energy=power; o.data.size=size; look(o,(0,0,0))
        elif shot=='cells':
            m=mesh('Unit cube',[(x,y,z) for x in (0,1) for y in (0,1) for z in (0,1)],[(0,1,3,2),(4,6,7,5),(0,4,5,1),(2,3,7,6),(0,2,6,4),(1,5,7,3)])
            self.objects=[object_('Carrier cell '+str(i),m,self.mats[i]) for i in range(7)]
            self.light_scale((1,1,1),1,-.55)
        elif shot=='periodic':
            self.objects=self.copies(D['periodic'],plain=True)
            for i,o in enumerate(self.objects): o.material_slots[0].material=self.mats[(i%25)%8]
            # Surface-strip outlines are projected in composition, with depth-independent labels.
            self.base_lines=[o.location.copy() for o in self.extra]
            self.light_scale((0,0,0),6,-8.1)
        elif shot=='restore':
            self.objects=self.copies(D['sigma'][0],plain=True,colors=False)+self.copies(D['sigma'][0],colors=False)
            self.objects[0].location.y=-1.7; self.objects[1].location.y=1.7
            self.light_scale((1,1,1),2,-.045)
        elif shot=='assembly':
            self.objects=self.copies(D['sigma'][1]); self.light_scale((2,2,1.8),2,-.05)
            self.extra=outline('Doubled carrier outline ',D['sigma'][0][0],2,self.gold,.014)
        elif shot=='contact_pair':
            identity=D['sigma'][0][0][0]
            self.objects=self.copies([[identity,tr] for tr in D['fixture']['translations']])
            self.objects[0].material_slots[0].material=self.coral; self.objects[1].material_slots[0].material=self.blue
            self.light_scale((2,.5,1),2,-.045)
            # Exact world-point locator is projected by compose.py; no duplicate 3D leader.
        elif shot=='growth':
            # Preserve literal original poses. Visibility changes, never coordinates.
            self.objects=self.copies(D['nested'][2]); self.light_scale((5,5,4),12,-10.05)
            self.level1={json.dumps(p) for p in D['nested'][1]}; self.level0=json.dumps(D['nested'][0][0])
            self.ranks=[]
            for p in D['nested'][2]:
                key=json.dumps(p)
                self.ranks.append(0 if key==self.level0 else 1 if key in self.level1 else 2)
        elif shot=='hierarchy':
            self.objects=self.copies(D['sigma'][2]); self.parents=self.copies(D['sigma'][1],scale=2)
            self.grand=self.copies(D['sigma'][0],scale=4,colors=False)
            for p in D['sigma'][1]: self.extra+=outline('Parent carrier ',p,2,self.gold,.025)
            self.light_scale((4,4,3.5),4,-.05)
        elif shot=='mirrors':
            self.objects=self.copies(D['sigma'][0],colors=False)+self.copies(D['sigma'][0],colors=False)
            self.objects[0].location.y=-2
            # Axis transposition is an exact reflection, determinant -1; carrier silhouette is unchanged.
            self.objects[1].matrix_world=Matrix(((0,1,0,0),(1,0,0,2),(0,0,1,0),(0,0,0,1)))
            self.light_scale((1,1,1),2,-.05)
        else: raise ValueError(shot)

    def update(self,t):
        shot=self.shot
        if shot in ('hero','outro','plain_hero'):
            local=t if shot=='hero' else t-24 if shot=='plain_hero' else t-228
            self.camera((1,1,.9),10.5,.4+local*.045,.53)
        elif shot=='opening_patch':
            self.camera((3.7,3.7,3.5),mix(43,47,smooth((t-6)/7)),.65+(t-6)*.018,.62)
        elif shot in ('macro','macro_restore'):
            local=t-13 if shot=='macro' else t-74
            flatten=smooth((t-21)/3) if shot=='macro' else 0
            if flatten:
                for v,orig,flat in zip(self.objects[0].data.vertices,self.macro_vertices,self.macro_flat):
                    v.co=tuple(mix(a,b,flatten) for a,b in zip(orig,flat))
                self.objects[0].data.update()
            # x is the face normal; tangential axis y runs horizontally.
            target=Vector((0,0,0)); self.cam.location=(2.8,-2.6,1.4)
            look(self.cam,target); self.cam.data.ortho_scale=4.1+local*.015
            if shot=='macro' and t>=24:
                p=smooth((t-24)/4)
                self.camera(tuple(mix(a,b,p) for a,b in zip((0,0,0),(-100,75,52.5))),mix(4.3,670,p),mix(-.75,.7,p),.5)
        elif shot=='cells':
            spread=.55*math.sin(math.pi*smooth((t-28)/8))
            for o,c in zip(self.objects,D['cells']): o.location=tuple(v+(v-.5)*spread for v in c)
            self.camera((1,1,.9),14,.66+(t-28)*.028,.62)
        elif shot=='periodic':
            self.camera((-.5,0,.2),48,.80,.66)
            for i,o in enumerate(self.objects):
                # Visibility reveal at exact poses, with no floating-position claim.
                o.hide_render=(t<40 and i/len(self.objects)>smooth((t-36)/4))
            if t<44: shift=0
            elif t<53: shift=smooth((t-45)/4)
            else: shift=1+smooth((t-53)/3)
            for o,base in zip(self.extra,self.base_lines):
                o.hide_render=t<44
                o.location=base+Vector(D['periodic_basis'][0])*shift
        elif shot=='restore':
            self.camera((1,1,1),17,.20+(t-66)*.012,.57)
        elif shot=='assembly':
            if self.scene.render.engine=='BLENDER_EEVEE_NEXT' and self.scene.render.resolution_x>=1920:
                self.scene.eevee.taa_render_samples=128 if 107<=t<115 else 64
            order=[7,0,4,2,6,1,5,3]
            for i,o in enumerate(self.objects):
                p=D['sigma'][1][i]; m=pose_matrix(p)
                if t<107:
                    o.hide_render=i!=7
                else:
                    rank=order.index(i); progress=smooth((t-107-rank*.75)/1.8)
                    o.hide_render=progress==0 and i!=7
                    center=m@Vector((.8,.8,.8)); direction=(center-Vector((2,2,2))).normalized()
                    if i==7: progress=1
                    m.translation+=direction*1.5*(1-progress)
                    o.material_slots[0].material=self.mats[i] if progress==1 else self.ghosts[i]
                o.matrix_world=m
            for o in self.extra: o.hide_render=t<116
            span=22 if t<107 else mix(22,32,smooth((t-107)/.7)) if t<114.2 else mix(32,22,smooth((t-114.2)/2))
            self.camera((2,2,1.8),span,.45+(t-100)*.022,.61)
        elif shot=='contact_pair':
            self.camera((2,.5,.9),16,-.7+(t-82)*.04,.55)
        elif shot=='growth':
            for o,p,rank in zip(self.objects,D['nested'][2],self.ranks):
                distance=max(abs(x) for x in p[1])
                threshold=123 if rank==0 else 124+distance*.42 if rank==1 else 132+distance*.22
                hidden=t<threshold
                if o.hide_render!=hidden: o.hide_render=hidden
                if t>=139 and not self.monocolor: o.material_slots[0].material=self.ivory
            if t>=139: self.monocolor=True
            if t<131: z=smooth((t-123)/1); center=(mix(1,1.4,z),)*3; span=mix(10.5,43,z)
            else: z=smooth((t-131)/1); center=(mix(1.4,4,z),)*3; span=mix(43,175,z)
            self.camera(center,span,.64+(min(t,146)-123)*.007,.66)
        elif shot=='hierarchy':
            for i,o in enumerate(self.objects):
                o.hide_render=t>=176
                o.material_slots[0].material=self.mats[i%8 if t<164 else (i//8)%8]
            for o in self.extra: o.hide_render=t<162 or t>=176
            for o in self.parents: o.hide_render=not 176<=t<180
            for o in self.grand: o.hide_render=t<180
            # Explicit cut replacement; these are standardized Q's, not literal union equality.
            self.camera((3.7,3.7,3.4),43,.75+(t-160)*.009,.64)
        elif shot=='mirrors':
            self.camera((1,1,1),20,.10+(t-207)*.012,.57)

def main():
    a=argparse.ArgumentParser(); a.add_argument('--shot',required=True); a.add_argument('--start',type=int,required=True); a.add_argument('--end',type=int,required=True)
    a.add_argument('--step',type=int,default=1); a.add_argument('--width',type=int,default=1920); a.add_argument('--samples',type=int,default=24); a.add_argument('--output',required=True)
    a.add_argument('--transparent',action='store_true')
    a.add_argument('--feature-map',action='store_true')
    a.add_argument('--camera-angle',type=float)
    a.add_argument('--camera-elevation',type=float)
    a.add_argument('--camera-span',type=float,default=10.5)
    a.add_argument('--projection-output')
    args=a.parse_args(sys.argv[sys.argv.index('--')+1:])
    out=Path(args.output); out.mkdir(parents=True,exist_ok=True)
    studio=Studio(args.shot,args.width,args.samples,args.transparent,args.feature_map)
    hold_path=None; previous_hold=None
    for frame in range(args.start,args.end,args.step):
        path=out/f'{frame:06d}.png'
        if path.exists(): continue
        hold='periodic_background' if args.shot=='periodic' and frame>=1200 else 'universal_claim_hold' if args.shot=='growth' and frame>=4380 else None
        if hold and hold==previous_hold and hold_path is not None:
            os.link(hold_path,path)
            print(json.dumps({'frame':frame,'intentional_static_hold_from':hold_path.name,'shot':args.shot}),flush=True)
            continue
        before=time.monotonic(); studio.update(frame/30)
        if args.camera_angle is not None and args.camera_elevation is not None:
            studio.camera((1,1,.9),args.camera_span,args.camera_angle,args.camera_elevation)
            # Orthographic audit views need a camera-facing key, including the
            # underside; this changes illumination only, never geometry.
            key=studio.lights[0][0]
            key.location=studio.cam.location
            key.data.energy=1200
            key.data.size=5
            look(key,(1,1,.9))
            if args.projection_output:
                bpy.context.view_layer.update()
                toward_camera=(studio.cam.location-Vector((1,1,.9))).normalized()
                projected=[]
                for patch in SOLID['patches']:
                    base=[Vector(tuple(float(Fraction(c)) for c in vertex)) for vertex in patch['base']]
                    apex=Vector(tuple(float(Fraction(c)) for c in patch['apex']))
                    centre=sum(base,Vector())/4
                    delta=apex-centre
                    outward=delta.normalized() if patch['coefficient']>0 else -delta.normalized()
                    if outward.dot(toward_camera)<.999:
                        continue
                    uv=world_to_camera_view(studio.scene,studio.cam,centre)
                    projected.append({'role':int(patch['role']),
                                      'panel':int(patch['face']),
                                      'coefficient':int(patch['coefficient']),
                                      'x':uv.x,'y':uv.y,'depth':uv.z})
                projection_path=Path(args.projection_output)
                projection_path.parent.mkdir(parents=True,exist_ok=True)
                projection_path.write_text(json.dumps({'width':args.width,
                                                        'height':args.width*9//16,
                                                        'features':projected},indent=2)+'\n')
        temporary=path.with_name(path.stem+'.render.png')
        studio.scene.render.filepath=str(temporary); bpy.ops.render.render(write_still=True)
        os.replace(temporary,path)
        print(json.dumps({'frame':frame,'seconds':round(time.monotonic()-before,3),'shot':args.shot}),flush=True)
        previous_hold=hold; hold_path=path if hold else None

if __name__=='__main__': main()
