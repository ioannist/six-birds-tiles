#!/usr/bin/env python3
"""Typography, exact section diagram, proof diagrams and H.264 composition.

Artwork is generated at 1920x1080. Caption-free retains explanatory labels.
Preview holds its 2-fps source samples; final consumes every 30-fps source frame.
"""
import argparse
from bisect import bisect_right
from functools import lru_cache
from fractions import Fraction
import json
import math
from pathlib import Path
import subprocess
import time
import wave
import numpy as np
from PIL import Image,ImageDraw,ImageFont
import imageio_ffmpeg
from timeline import FPS,DURATION,DIAGRAMS,shot_at,labels
from projection import project
HERE=Path(__file__).resolve().parent
CAPTIONS=json.loads((HERE/'captions.json').read_text())
CONFIG=json.loads((HERE/'scene_config.json').read_text())
DATA=json.loads((HERE/'.cache/scene_data.json').read_text())
SOLID=json.loads((HERE/'.cache/source/solid/r44_solid.json').read_text())
LEVEL1={json.dumps(p) for p in DATA['nested'][1]}
LEVEL0=json.dumps(DATA['nested'][0][0])
GROWTH_TIMES=sorted(123 if json.dumps(p)==LEVEL0 else 124+max(abs(x) for x in p[1])*.42 if json.dumps(p) in LEVEL1 else 132+max(abs(x) for x in p[1])*.22 for p in DATA['nested'][2])
W,H=1920,1080
INK='#1b2540'; WHITE='#f4ecdf'; MUTED='#c9cfe0'; GOLD='#f3b53a'; BLUE='#5aa9e6'; CORAL='#e8563f'
FONT=Path('/usr/share/fonts/truetype/dejavu')
WAIT_FOR_FRAMES=False
@lru_cache(None)
def font(size,bold=False): return ImageFont.truetype(str(FONT/('DejaVuSans-Bold.ttf' if bold else 'DejaVuSans.ttf')),size)
@lru_cache(None)
def serif_font(size,bold=False): return ImageFont.truetype(str(FONT/('DejaVuSerif-Bold.ttf' if bold else 'DejaVuSerif.ttf')),size)
def text(d,xy,s,size=32,fill=WHITE,bold=False,anchor=None): d.text(xy,s,font=font(size,bold),fill=fill,anchor=anchor)
def serif_text(d,xy,s,size=32,fill=WHITE,bold=False,anchor=None): d.text(xy,s,font=serif_font(size,bold),fill=fill,anchor=anchor)
def arrow(d,a,b,fill=GOLD,width=5):
    d.line([a,b],fill=fill,width=width)
    v=np.array(b,dtype=float)-np.array(a,dtype=float); norm=np.linalg.norm(v)
    if norm<1: return
    v=v/norm; n=np.array([-v[1],v[0]]); end=np.array(b)
    d.polygon([tuple(end),tuple(end-v*18+n*9),tuple(end-v*18-n*9)],fill=fill)

def strip_outline(d,t):
    smooth=lambda x: (lambda z:z*z*(3-2*z))(max(0,min(1,x)))
    shift=smooth((t-45)/4) if t<53 else 1+smooth((t-53)/3)
    view=(math.cos(.8)*math.cos(.66),math.sin(.8)*math.cos(.66),math.sin(.66))
    lines=[]
    for _,tr in DATA['periodic_motif']:
        for face in DATA['plain_faces']:
            v=[np.array(DATA['plain_vertices'][i],dtype=float) for i in face]
            normal=np.cross(v[1]-v[0],v[2]-v[0])
            if normal@view<=0: continue
            points=[project(p+tr+np.array(DATA['periodic_basis'][0])*shift,(-.5,0,.2),48,.8,.66) for p in v]
            lines.append(points+[points[0]])
    # Deliberate diagram overlay: complete projected front-facing edges, no depth clipping.
    for points in lines: d.line(points,fill='#29303a',width=8,joint='curve')
    for points in lines: d.line(points,fill=GOLD,width=4,joint='curve')
@lru_cache(None)
def background():
    y,x=np.mgrid[:H,:W]; fall=np.exp(-(((x-W*.54)/1100)**2+((y-H*.58)/760)**2))
    a=np.zeros((H,W,3),dtype=np.uint8)
    for i,(base,glow) in enumerate(zip((18,26,47),(16,22,34))): a[:,:,i]=base+fall*glow
    return Image.fromarray(a)

def editorial_motif(d):
    """Website-derived framing; editorial decoration, never tile geometry."""
    d.pieslice((-310,-330,430,410),0,360,fill='#26325a')
    d.pieslice((-260,-280,330,310),0,360,fill='#f4ecdf')
    d.arc((-310,-330,430,410),0,360,fill=GOLD,width=3)
    d.pieslice((1510,720,2130,1340),180,270,fill='#26325a')
    d.arc((1510,720,2130,1340),180,270,fill=GOLD,width=3)

def feature_map_card(d,box=(1300,305,1780,805),compact=False):
    """One canonical panel as a flat annotation, never substitute geometry."""
    x0,y0,x1,y1=box
    d.rounded_rectangle(box,radius=18,fill='#f4ecdf',outline=GOLD,width=3)
    text(d,(x0+24,y0+22),'FEATURE MAP' if compact else 'FEATURE MAP · ANNOTATION',15 if compact else 21,INK,True)
    # Panel 13 faces -y, so its increasing-coordinate tangent axes are x,z.
    # Read its actual feature centres and coefficients from the pinned rational
    # solid instead of maintaining an illustrative copy of its sign pattern.
    features=[]
    for patch in SOLID['patches']:
        if patch['face'] != 13:
            continue
        centre=[sum((Fraction(v) for v in axis),Fraction())/4 for axis in zip(*patch['base'])]
        features.append((int(patch['coefficient']),float(centre[0]%1),float(centre[2]%1)))
    assert len(features)==8 and {abs(a) for a,_,_ in features}=={9,10,11,12}
    top=y0+(72 if compact else 86); side=min(x1-x0-54,y1-top-54); ox=(x0+x1-side)/2
    for a,u,v in features:
        x=ox+u*side; y=top+v*side; r=7 if compact else 10
        if a>0: d.rectangle((x-r,y-r,x+r,y+r),fill=CORAL)
        else: d.rectangle((x-r,y-r,x+r,y+r),fill='#f4ecdf',outline=BLUE,width=4)
    if not compact: text(d,((x0+x1)//2,y1-35),'filled coral: bump  ·  hollow sky: dent',18,INK,False,'mm')

def section(im,t):
    d=ImageDraw.Draw(im)
    left,right,top,bottom=300,1620,325,770
    d.rounded_rectangle((left-30,top-30,right+30,bottom+30),radius=20,fill='#142536',outline='#36516a',width=2)
    # One uniform pixels-per-unit factor for both axes. No vertical exaggeration.
    scale=24000; cx=960; cy=560
    profile=[(float(Fraction(u)),float(Fraction(a)),float(Fraction(b))) for u,a,b in DATA['section']]
    upper=[(cx+u*scale,cy-a*scale) for u,a,b in profile]
    lower=[(cx+u*scale,cy-b*scale) for u,a,b in profile]
    d.polygon([(left,top),(right,top),*lower[::-1]],fill='#315d79')
    d.polygon([*upper,(right,bottom),(left,bottom)],fill='#884f46')
    d.polygon([*upper,*lower[::-1]],fill=GOLD)
    d.line(upper,fill='#ffb4a0',width=3); d.line(lower,fill='#97d9fc',width=3)
    for x in range(left,right,25): d.line((x,cy,min(x+12,right),cy),fill='#d3d8dc',width=1)
    text(d,(350,350),'COPY B',26,bold=True); text(d,(350,390),'solid lies above its boundary',27)
    text(d,(350,655),'COPY A',26,bold=True); text(d,(350,697),'solid lies below its boundary',27)
    arrow(d,(1230,440),(990,552)); text(d,(1240,408),'OVERLAP',29,GOLD,True)
    text(d,(1240,450),'Shared interior',28,GOLD)
    text(d,(960,832),'Section through (2, 1/4, 3/8) · same scale on both axes',28,MUTED,anchor='mm')
    if t>=93:
        d.rounded_rectangle((570,235,1350,285),radius=12,fill='#713c35')
        text(d,(960,258),'ONE ARRANGEMENT RULED OUT',26,WHITE,True,'mm')

def proof(im,t):
    d=ImageDraw.Draw(im)
    for i,(x,label,vector) in enumerate([(155,'T','p'),(725,'D(T)','p/2'),(1295,'D²(T)','p/4')]):
        d.rounded_rectangle((x,300,x+470,735),radius=20,fill='#122638',outline='#30465c',width=2)
        text(d,(x+235,343),label,38,WHITE,True,'mm')
        for gx in range(x+55,x+430,60): d.line((gx,405,gx,660),fill='#294457',width=2)
        for gy in range(420,680,60): d.line((x+40,gy,x+430,gy),fill='#294457',width=2)
        length=240/(2**i)
        arrow(d,(x+70,540),(x+70+length,540))
        text(d,(x+235,693),vector,38,GOLD,False,'mm')
        if i<2:
            arrow(d,(x+490,520),(x+550,520),MUTED,3)
            text(d,(x+520,480),'÷2',26,MUTED,anchor='mm')
    if t<192: formula='The same hypothetical period descends with the hierarchy.'
    elif t<200: formula='At every level:  p/2ⁿ ∈ ℤ³'
    else: formula='p/2ⁿ ∈ ℤ³  for every n   ⇒   p = 0'
    text(d,(960,806),formula,38,GOLD if t>=200 else WHITE,True if t>=200 else False,'mm')
    text(d,(960,855),'Illustration only: 4 → 2 → 1 → 1/2 (not an integer)' if t>=200 else 'Grid illustration · arrows show the halving relation',26,MUTED,anchor='mm')

def symmetry(im,t):
    d=ImageDraw.Draw(im)
    text(d,(550,505),'≤24',170,GOLD,True,'mm')
    text(d,(550,650),'symmetries of any tiling',34,WHITE,anchor='mm')
    # Schematic screw with nonzero axial motion, never a false contact experiment.
    pts=[]
    for a in np.linspace(0,math.pi*4,180): pts.append((1320+85*math.cos(a),700-a*25+24*math.sin(a)))
    d.line(pts,fill=BLUE,width=7); arrow(d,(1320,735),(1320,335),MUTED,3)
    d.line((1170,700,1480,345),fill=CORAL,width=10)
    text(d,(1320,765),'No screw symmetry',33,WHITE,anchor='mm')
    text(d,(1320,806),'with a nonzero slide',31,WHITE,anchor='mm')

# Shared with the layout audit so the actual card typography is checked.
END_CARD_LINES=[
    (960,290,'Chair44 (R44)',100,GOLD,True),
    (960,390,'One shape. No periodic tiling.',40,WHITE,False),
    (960,510,CONFIG['author'],42,WHITE,True),
    (960,578,CONFIG['credit'],34,MUTED,False),
    (960,710,CONFIG['website_display'],48,GOLD,True),
    (960,817,'Explore the tile · Run the notebook · Check the proof',30,WHITE,False),
]

def endcard(im,t):
    d=ImageDraw.Draw(im)
    editorial_motif(d)
    for i,(x,y,copy,size,colour,bold) in enumerate(END_CARD_LINES):
        (serif_text if i==0 else text)(d,(x,y),copy,size,colour,bold,'mm')
    d.line((720,445,1200,445),fill='#375670',width=2)

@lru_cache(maxsize=3)
def read_frame(path):
    if WAIT_FOR_FRAMES:
        deadline=time.monotonic()+3600
        while not Path(path).exists():
            if time.monotonic()>deadline: raise TimeoutError(f'Render did not produce {path}')
            time.sleep(.05)
    return Image.open(path).convert('RGB').resize((W,H),Image.Resampling.LANCZOS)

def artwork(frame,quality):
    t=frame/FPS; name,_,_=shot_at(t)
    if name in DIAGRAMS:
        im=background().copy()
        {'section':section,'proof':proof,'symmetry':symmetry,'endcard':endcard}[name](im,t)
    else:
        src=frame if quality=='final' else frame//15*15
        im=read_frame(str(HERE/'output'/quality/'frames'/f'{src:06d}.png')).copy()
    return im

def overlay(im,frame,captioned=True,clock=True):
    t=frame/FPS; name,_,_=shot_at(t)
    im=im.convert('RGBA'); top=Image.new('RGBA',(W,H)); d=ImageDraw.Draw(top)
    # Quiet gradients separate prose from the studio without a heavy boxed layout.
    for y in range(240): d.line((0,y,W,y),fill=(27,37,64,int(235 if y<=205 else 235*(240-y)/35)))
    for y in range(875,H): d.line((0,y,W,y),fill=(27,37,64,int(220*min(1,(y-875)/80))))
    if name!='endcard':
        kicker,title,label=labels(t)
        text(d,(120,45),kicker,24,GOLD,True)
        text(d,(116,84),title,54,WHITE,True)
        text(d,(120,161),label,28,MUTED)
        d.line((120,210,1800,210),fill='#314454',width=1)
    if clock: text(d,(1800,49),f'{int(t)//60}:{int(t)%60:02d} / {DURATION//60}:{DURATION%60:02d}',23,MUTED,anchor='ra')
    if name=='periodic' and t>=44:
        strip_outline(d,t)
        # The highlighted, moving motif lies in a verified two-step buffered lattice.
        d.rounded_rectangle((1170,710,1790,851),radius=15,fill=(6,19,31,230),outline=GOLD,width=2)
        text(d,(1200,730),'Surface strip · projected outline',27,WHITE,True)
        arrow(d,(1210,810),(1380,785)); text(d,(1420,786),'b₁ = (−2, 1, 0)',28,GOLD)
        if 49<=t<53 or t>=56: text(d,(120,792),'✓  Exact alignment',34,GOLD,True)
    if name=='contact_pair':
        x,y=project((2,.25,.375),(2,.5,.9),16,-.7+(t-82)*.04,.55)
        d.ellipse((x-19,y-19,x+19,y+19),outline='#172231',width=9)
        d.ellipse((x-19,y-19,x+19,y+19),outline=GOLD,width=5)
        d.line((x+18,y-10,x+150,y-125),fill=GOLD,width=4)
        text(d,(x+160,y-145),'SECTION',25,GOLD,True)
    if name=='macro_restore':
        feature_map_card(d)
    if name=='growth':
        count=bisect_right(GROWTH_TIMES,t)
        d.rounded_rectangle((100,750,570,884),radius=12,fill=(6,19,31,240))
        text(d,(120,770),f'{count:,}',64,GOLD,True)
        text(d,(122,845),'copies · one material' if t>=139 else 'actual copy of Chair44' if count==1 else 'actual copies of Chair44',27,MUTED)
    if name=='hierarchy':
        first,second=('64 copies','8 carrier groups') if t<176 else ('Standardized Q copies','Scale 2') if t<180 else ('Standardized Q copy','Scale 4')
        d.rounded_rectangle((100,728,610,858),radius=12,fill=(6,19,31,240))
        text(d,(125,750),first,30,GOLD,True); text(d,(125,802),second,30,WHITE)
    if captioned:
        cue=next((c for c in CAPTIONS if c['start']<=t<c['end']),None)
        lines=cue['text'].splitlines() if cue else []
        for i,line in enumerate(lines): text(d,(960,934+i*60 if len(lines)==2 else 960),line,48,WHITE,False,'mm')
    if clock:
        d.line((120,1048,1800,1048),fill='#304357',width=3)
        d.line((120,1048,120+1680*t/DURATION,1048),fill=GOLD,width=3)
    return Image.alpha_composite(im,top).convert('RGB')

def srt():
    def timestamp(s): return f'{int(s)//3600:02}:{int(s)//60%60:02}:{int(s)%60:02},000'
    last=0; blocks=[]
    for c in CAPTIONS:
        assert c['start']==last and c['end']>last
        assert len(c['text'].splitlines())<=2 and max(map(len,c['text'].splitlines()))<=48
        assert len(c['text'].split())/(c['end']-c['start'])<=3
        blocks.append(f"{c['id']}\n{timestamp(c['start'])} --> {timestamp(c['end'])}\n{c['text']}\n")
        last=c['end']
    assert last==DURATION-6  # The final six seconds are a caption-free credit hold.
    (HERE/'CAPTIONS.srt').write_text('\n'.join(blocks))

def soundtrack():
    path=HERE/'output/ambient.wav'
    if path.exists():
        with wave.open(str(path),'rb') as existing:
            if existing.getnframes()==existing.getframerate()*DURATION: return path
    rate=48000; total=rate*DURATION; music=np.zeros((total,2),np.float32)
    # Original procedural pad: no samples, recordings or external music.
    chords=[(146.832,220,293.665),(130.813,196,261.626),(174.614,220,349.228),(110,164.814,220)]
    for k,start in enumerate(range(0,DURATION,8)):
        length=min(12,DURATION-start); tt=np.arange(length*rate)/rate
        env=np.minimum(1,tt/2)*np.minimum(1,(length-tt)/4)
        for j,f in enumerate(chords[k%4]):
            tone=(np.sin(2*np.pi*f*tt)+.18*np.sin(2*np.pi*f*2*tt))*.008*env
            music[start*rate:start*rate+len(tt),j%2]+=tone
            music[start*rate:start*rate+len(tt),1-j%2]+=tone*.7
    fade=np.minimum(1,np.arange(total)/rate/3)*np.minimum(1,(total-np.arange(total))/rate/4)
    music*=fade[:,None]
    with wave.open(str(path),'wb') as f:
        f.setnchannels(2); f.setsampwidth(2); f.setframerate(rate); f.writeframes((music*32767).astype('<i2').tobytes())
    return path

def main():
    global WAIT_FOR_FRAMES
    p=argparse.ArgumentParser(); p.add_argument('--quality',choices=['preview','final'],default='preview'); p.add_argument('--clean',action='store_true'); p.add_argument('--stills',nargs='*',type=float)
    p.add_argument('--time-range',nargs=2,type=float,default=[0,DURATION]); p.add_argument('--output-name')
    p.add_argument('--wait-frames',action='store_true'); p.add_argument('--skip-srt',action='store_true')
    a=p.parse_args(); WAIT_FOR_FRAMES=a.wait_frames
    if not a.skip_srt: srt()
    out=HERE/'output'/a.quality; out.mkdir(exist_ok=True)
    if a.stills:
        for t in a.stills:
            frame=int(t*FPS); overlay(artwork(frame,a.quality),frame,not a.clean).save(out/f'still_{t:06.2f}.jpg',quality=95)
        return
    movie=out/(a.output_name or ('r44_clean.mp4' if a.clean else 'r44_captioned.mp4'))
    ff=imageio_ffmpeg.get_ffmpeg_exe(); audio=soundtrack()
    # Preview is honest 2-fps motion sampling encoded at 30 fps; final is native 30 fps.
    output_fps=2 if a.quality=='preview' else FPS
    cmd=[ff,'-y','-v','warning','-f','rawvideo','-vcodec','rawvideo','-pix_fmt','rgb24','-s','1920x1080','-r',str(output_fps),'-i','-','-ss',str(a.time_range[0]),'-i',str(audio),'-c:v','libx264','-preset','fast','-crf','18','-pix_fmt','yuv420p','-r','30','-threads','8','-c:a','aac','-b:a','192k','-af','volume=4','-metadata','comment=R44 procedural audio gain x4','-t',str(a.time_range[1]-a.time_range[0]),'-movflags','+faststart',str(movie)]
    proc=subprocess.Popen(cmd,stdin=subprocess.PIPE)
    try:
        for frame in range(int(a.time_range[0]*FPS),int(a.time_range[1]*FPS),FPS//output_fps):
            proc.stdin.write(overlay(artwork(frame,a.quality),frame,not a.clean).tobytes())
            if frame%900==0: print('Composed',frame/FPS,'seconds',flush=True)
    finally:
        proc.stdin.close()
    if proc.wait(): raise RuntimeError('FFmpeg failed')
    print(movie)
if __name__=='__main__': main()
