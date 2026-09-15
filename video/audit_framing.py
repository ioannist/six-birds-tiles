"""Measure graphics-space framing at editorial checkpoints (not a geometric proof)."""
import json
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import bpy
from bpy_extras.object_utils import world_to_camera_view
from mathutils import Vector
from build_scene import Studio

SHOTS={'hero':[0,3,5.99],'opening_patch':[6,9,12.99],'plain_hero':[24,27.99],
 'cells':[28,32,35.99],'periodic':[40,48,57],'restore':[66,73.99],
 'contact_pair':[82,85.99],'assembly':[100,107,111,115,122.99],
 'growth':[123,124,127,131,132,135,138,143,150,159.99],
 'hierarchy':[160,164,178,182,183.99],'mirrors':[207,220.99],'outro':[228,233.99]}

def main():
    records=[]
    for name,times in SHOTS.items():
        s=Studio(name,960,8)
        for t in times:
            s.update(t); bpy.context.view_layer.update()
            objects=s.objects+getattr(s,'parents',[])+getattr(s,'grand',[])
            points=[world_to_camera_view(s.scene,s.cam,o.matrix_world@Vector(v)) for o in objects if not o.hide_render for v in o.bound_box]
            if not points: continue
            bounds=[min(p.x for p in points)*1920,(1-max(p.y for p in points))*1080,max(p.x for p in points)*1920,(1-min(p.y for p in points))*1080]
            records.append({'shot':name,'time':t,'bounds_pixels':[round(x,1) for x in bounds]})
    failures=[r for r in records if r['bounds_pixels'][1]<225 or r['bounds_pixels'][3]>890]
    (HERE/'FRAMING_CHECKS.json').write_text(json.dumps({'scope':'Conservative projected mesh bounding boxes; macro intentionally fills the screen; travel is illustrative.',
        'checkpoints':records,'safe_vertical_interval_pixels':[225,890],'failed_checkpoints':failures,'status':'FAIL' if failures else 'PASS'},indent=2)+'\n')
    assert not failures,failures
    print('PASS: all editorial framing checkpoints')
if __name__=='__main__': main()
