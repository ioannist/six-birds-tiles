#!/usr/bin/env python3
"""Resumable render driver; the preview uses 2 fps samples, the master true 30 fps."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from timeline import SHOTS,DIAGRAMS
HERE=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(); p.add_argument('--quality',choices=['preview','final'],default='preview'); p.add_argument('--shots',nargs='*'); p.add_argument('--frames',nargs='*',type=int)
    p.add_argument('--time-range',nargs=2,type=float)
    args=p.parse_args()
    receipt=json.loads((HERE/'DATA_CHECKS.json').read_text())
    for path,digest in receipt['canonical_sha256'].items():
        assert hashlib.file_digest((HERE/'.cache/source'/path).open('rb'),'sha256').hexdigest()==digest
    assert hashlib.file_digest((HERE/'.cache/scene_data.json').open('rb'),'sha256').hexdigest()==receipt['render_data_sha256']
    width,samples,step=(960,8,15) if args.quality=='preview' else (1920,24,1)
    out=HERE/'output'/args.quality/'frames'; out.mkdir(parents=True,exist_ok=True)
    blender=HERE/'.tools/blender-4.5.13-linux-x64/blender'
    env=dict(os.environ,CUDA_VISIBLE_DEVICES=os.environ.get('R44_VIDEO_GPU','3'),OMP_NUM_THREADS='12')
    for name,a,b in SHOTS:
        if name in DIAGRAMS or (args.shots and name not in args.shots): continue
        intervals=[(a*30,b*30)] if not args.frames else [(f,f+1) for f in args.frames if a*30<=f<b*30]
        for start,end in intervals:
            if args.time_range: start=max(start,int(args.time_range[0]*30)); end=min(end,int(args.time_range[1]*30))
            if start>=end: continue
            if all((out/f'{f:06d}.png').exists() for f in range(start,end,step)): continue
            log=out.parent/f'{name}_{start}.log'
            provenance={'shot':name,'start':start,'end_exclusive':end,'step':step,'resolution_width':width,
                'source_commit':receipt['source_commit'],'scene_data_sha256':receipt['render_data_sha256'],
                'scene_script_sha256':hashlib.file_digest((HERE/'build_scene.py').open('rb'),'sha256').hexdigest(),
                'gpu_requested':env['CUDA_VISIBLE_DEVICES'],'engine':env.get('R44_VIDEO_ENGINE','EEVEE')}
            log.with_suffix('.json').write_text(json.dumps(provenance,indent=2)+'\n')
            print(f'Rendering {args.quality}: {name}, frames {start}..{end-1}',flush=True)
            cmd=[str(blender),'-b','--factory-startup','--python',str(HERE/'build_scene.py'),'--','--shot',name,'--start',str(start),'--end',str(end),'--step',str(step),'--width',str(width),'--samples',str(samples),'--output',str(out)]
            with log.open('w') as f: subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
    print('Render stage complete.',flush=True)
if __name__=='__main__': main()
