"""Blender-side audit of delivered poses and motion endpoints; no rendering."""
import json
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from build_scene import Studio,D,pose_matrix
from projection import project
import bpy
from mathutils import Vector
from bpy_extras.object_utils import world_to_camera_view

def main():
    checks={}
    s=Studio('assembly',960,8)
    for t in (115,116,120,122.99):
        s.update(t)
        for o,p in zip(s.objects,D['sigma'][1]):
            assert o.matrix_world==pose_matrix(p),(t,o.name,'noncanonical settled pose')
            assert not o.hide_render
    checks['assembly_all_settled_poses']='PASS at 115, 116, 120, 122.99 seconds'
    s=Studio('growth',960,8)
    counts=[]
    for t,expected in [(123,1),(127,64),(131,64),(138,4096),(143,4096),(159.99,4096)]:
        s.update(t); count=sum(not o.hide_render for o in s.objects)
        assert count==expected,(t,count,expected)
        for o,p in zip(s.objects,D['nested'][2]): assert o.matrix_world==pose_matrix(p)
        counts.append([t,count])
    checks['growth_visible_counts']=counts
    checks['nested_world_poses_unchanged']='PASS'
    s=Studio('mirrors',960,8)
    assert s.objects[0].matrix_world.to_3x3().determinant()==1
    assert s.objects[1].matrix_world.to_3x3().determinant()==-1
    checks['displayed_handedness']=[1,-1]
    # The matrix convention is checked on the basis for every canonical pose.
    for poses in D['sigma']+D['nested']:
        for p in poses:
            (perm,sign),tr=p; m=pose_matrix(p)
            for i in range(3):
                assert m[i][3]==tr[i]
                for j in range(3): assert m[i][j]==(sign[i] if j==perm[i] else 0)
    checks['signed_permutation_convention']='PASS'
    errors=[]
    for name,t,center,span,angle,elevation in [('periodic',48,(-.5,0,.2),48,.8,.66),('contact_pair',84,(2,.5,.9),16,-.62,.55)]:
        s=Studio(name,960,8); s.update(t); bpy.context.view_layer.update()
        for point in [(2,.25,.375),(0,0,0),(-2,1,0),(2,2,2)]:
            actual=world_to_camera_view(s.scene,s.cam,Vector(point))
            predicted=project(point,center,span,angle,elevation)
            errors.append(max(abs(actual.x*1920-predicted[0]),abs((1-actual.y)*1080-predicted[1])))
    assert max(errors)<.01,errors
    checks['overlay_projection_max_error_pixels']=max(errors)
    checks['projection_scope']='Graphics alignment only; tolerance is not a geometric validity predicate.'
    checks['scope']='Rendering-state audit of exact integer poses; no new global tiling proof.'
    (HERE/'SCENE_CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(checks))
if __name__=='__main__': main()
