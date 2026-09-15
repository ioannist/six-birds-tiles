#!/usr/bin/env python3
"""Make the 40-second teaser, thumbnail, portable subtitles and delivery manifest."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
from PIL import Image,ImageDraw
from compose import HERE,FPS,DURATION,CONFIG,artwork,overlay,background,text,serif_text,feature_map_card,editorial_motif,WHITE,GOLD,MUTED,imageio_ffmpeg,soundtrack

CUTS=[
 (0,4,'One shape. Three dimensions.'),
 (46,50,'This similar chair repeats.'),
 (86,91,'Tiny features break that arrangement.'),
 (115,121,'Chair44 fits: eight compatible copies.'),
 (133,139,'Larger patches grow into space.'),
 (200,204,'The proof excludes periods at every scale.'),
 (228,233,'An aperiodic monotile. Shape alone.'),
 (234,240,'Explore the tile. Check the proof.')]

def make_thumbnail(out):
    im=background().copy()
    editorial_motif(ImageDraw.Draw(im))
    shifted=im.copy(); shifted.paste(artwork(90,'final'),(330,0))
    mask=Image.new('L',im.size); md=ImageDraw.Draw(mask)
    for x in range(1920): md.line((x,0,x,1080),fill=int(255*max(0,min(1,(x-480)/500))))
    im=Image.composite(shifted,im,mask)
    d=ImageDraw.Draw(im)
    serif_text(d,(120,100),'Chair44 (R44)',70,GOLD,True)
    for i,line in enumerate(['ONE SHAPE.','NO PERIODIC','TILING.']): text(d,(120,310+i*95),line,66,WHITE,True)
    text(d,(120,835),'A 3D aperiodic monotile',36,WHITE)
    text(d,(120,930),f"{CONFIG['author']} · {CONFIG['credit']} · {CONFIG['website_display'].removeprefix('www.')}",20,MUTED)
    feature_map_card(d,(1585,245,1850,635),True)
    im.save(out/'thumbnail.jpg',quality=96)

def make_teaser(out):
    ff=imageio_ffmpeg.get_ffmpeg_exe()
    duration=sum(b-a for a,b,_ in CUTS); assert duration==40
    movie=out/'r44_teaser_40s.mp4'
    cmd=[ff,'-y','-v','warning','-f','rawvideo','-pix_fmt','rgb24','-s','1920x1080','-r','30','-i','-','-i',str(soundtrack()),'-c:v','libx264','-preset','fast','-crf','18','-pix_fmt','yuv420p','-threads','8','-c:a','aac','-b:a','192k','-af','volume=4,afade=t=out:st=36:d=4','-metadata','comment=R44 procedural audio gain x4','-t','40','-movflags','+faststart',str(movie)]
    proc=subprocess.Popen(cmd,stdin=subprocess.PIPE)
    try:
        for a,b,caption in CUTS:
            for frame in range(a*FPS,b*FPS):
                im=overlay(artwork(frame,'final'),frame,False,False)
                d=ImageDraw.Draw(im); text(d,(960,960),caption,48,WHITE,False,'mm')
                proc.stdin.write(im.tobytes())
    finally: proc.stdin.close()
    if proc.wait(): raise RuntimeError('Teaser encode failed')

def write_manifest(out):
    ff=imageio_ffmpeg.get_ffmpeg_exe()
    files=['r44_captioned.mp4','r44_clean.mp4','r44_teaser_40s.mp4','thumbnail.jpg','r44.srt']
    manifest={
        'revision':CONFIG['revision'],
        'title':CONFIG['title'],
        'source_commit':json.loads((HERE/'DATA_CHECKS.json').read_text())['source_commit'],
        'master':{'duration_seconds':DURATION,'resolution':[1920,1080],'fps':30},
        'teaser':{'duration_seconds':40,'cuts':CUTS},
        'outputs':{name:{'bytes':(out/name).stat().st_size,'sha256':hashlib.file_digest((out/name).open('rb'),'sha256').hexdigest()} for name in files},
        'production_sources':{p.name:hashlib.file_digest(p.open('rb'),'sha256').hexdigest() for p in sorted(HERE.iterdir()) if p.suffix in ('.py','.json','.srt') and p.name!='DELIVERY_CHECKS.json'},
        'ffmpeg':subprocess.check_output([ff,'-version'],text=True).splitlines()[0],
        'scope':'Locally produced media; no public upload or publication performed.'}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')

def main():
    parser=argparse.ArgumentParser()
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument('--thumbnail-only',action='store_true')
    modes.add_argument('--assets-only',action='store_true',help='Build teaser, thumbnail and subtitles while masters encode')
    modes.add_argument('--manifest-only',action='store_true',help='Refresh hashes after delivery review')
    args=parser.parse_args()
    out=HERE/'output/final'; ff=imageio_ffmpeg.get_ffmpeg_exe()
    if args.thumbnail_only: make_thumbnail(out); return
    if args.manifest_only: write_manifest(out); return
    if not args.assets_only:
        # Upgrade an already-running first composition without re-encoding its video.
        # The metadata marker makes this idempotent and future compose.py writes it directly.
        for name in ['r44_captioned.mp4','r44_clean.mp4']:
            path=out/name
            probe=subprocess.run([ff,'-hide_banner','-i',str(path)],capture_output=True,text=True).stderr
            if 'R44 procedural audio gain x4' not in probe:
                temp=path.with_name(path.stem+'.audio.mp4')
                subprocess.run([ff,'-v','error','-y','-i',str(path),'-c:v','copy','-af','volume=4','-c:a','aac','-b:a','192k','-metadata','comment=R44 procedural audio gain x4','-t',str(DURATION),'-movflags','+faststart',str(temp)],check=True)
                temp.replace(path)
    make_teaser(out)
    make_thumbnail(out)
    shutil.copyfile(HERE/'CAPTIONS.srt',out/'r44.srt')
    if not args.assets_only: write_manifest(out)
    print(out)
if __name__=='__main__': main()
