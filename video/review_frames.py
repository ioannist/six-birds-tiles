#!/usr/bin/env python3
"""Decode the encoded movie into timestamped review sheets and full-size frames."""
import argparse
from pathlib import Path
import subprocess
from PIL import Image,ImageDraw,ImageFont
import imageio_ffmpeg
FONT='/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf'
def main():
    p=argparse.ArgumentParser(); p.add_argument('movie',type=Path); p.add_argument('output',type=Path); p.add_argument('--fps',type=float,default=2)
    p.add_argument('--start',type=float,default=0); p.add_argument('--duration',type=float)
    a=p.parse_args(); a.output.mkdir(parents=True,exist_ok=True)
    ff=imageio_ffmpeg.get_ffmpeg_exe()
    cmd=[ff,'-v','error','-ss',str(a.start),'-i',str(a.movie)]
    if a.duration is not None: cmd+=['-t',str(a.duration)]
    proc=subprocess.Popen(cmd+['-vf',f'fps={a.fps},scale=400:225','-f','rawvideo','-pix_fmt','rgb24','-'],stdout=subprocess.PIPE)
    i=0; sheet=None; draw=None
    while True:
        raw=proc.stdout.read(400*225*3)
        if not raw: break
        if len(raw)!=400*225*3: raise RuntimeError('Partial decoded review frame')
        if i%24==0: sheet=Image.new('RGB',(1600,1530),'#07111e'); draw=ImageDraw.Draw(sheet)
        col,row=i%4,(i%24)//4
        sheet.paste(Image.frombytes('RGB',(400,225),raw),(col*400,row*255))
        draw.text((col*400+10,row*255+229),f'{a.start+i/a.fps:.2f}s',font=ImageFont.truetype(FONT,18),fill='white')
        if i%24==23: sheet.save(a.output/f'sheet_{i//24:02d}.jpg',quality=92)
        i+=1
    if i%24: sheet.save(a.output/f'sheet_{i//24:02d}.jpg',quality=92)
    if proc.wait(): raise RuntimeError('Decode failed')
    key_times=[3,9,17,23,26,32,48,57,78,84,88,111,120,127,138,143,164,178,196,203,218,223,237]
    key_times=[t for t in key_times if a.start<=t<a.start+i/a.fps]
    for t in key_times:
        subprocess.run([ff,'-v','error','-y','-ss',str(t),'-i',str(a.movie),'-frames:v','1','-q:v','2',str(a.output/f'key_{t:03d}.jpg')],check=True)
    print(f'Decoded {i} temporal samples and {len(key_times)} full-size frames from {a.movie}')
if __name__=='__main__': main()
