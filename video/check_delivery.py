#!/usr/bin/env python3
"""Decode every delivered movie frame, audit captions, inputs and safe file manifest."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import numpy as np
from PIL import Image,ImageDraw
from compose import HERE,CAPTIONS,END_CARD_LINES,font,serif_font,srt,imageio_ffmpeg
from timeline import SHOTS,DIAGRAMS,labels,DURATION

def main():
    srt()
    out=HERE/'output/final'; receipt=json.loads((HERE/'DATA_CHECKS.json').read_text())
    assert json.loads((HERE/'FRAMING_CHECKS.json').read_text())['status']=='PASS'
    for p,h in receipt['canonical_sha256'].items(): assert hashlib.file_digest((HERE/'.cache/source'/p).open('rb'),'sha256').hexdigest()==h
    assert hashlib.file_digest((HERE/'.cache/scene_data.json').open('rb'),'sha256').hexdigest()==receipt['render_data_sha256']
    ff=imageio_ffmpeg.get_ffmpeg_exe(); media={}
    for name,duration in [('r44_captioned.mp4',DURATION),('r44_clean.mp4',DURATION),('r44_teaser_40s.mp4',40)]:
        path=out/name
        probe=subprocess.run([ff,'-hide_banner','-i',str(path)],capture_output=True,text=True).stderr
        assert '1920x1080' in probe and '30 fps' in probe,(name,probe)
        expected=f'Duration: 00:{duration//60:02d}:{duration%60:02d}.00'
        assert expected in probe,(name,probe)
        decoded=subprocess.run([ff,'-v','error','-i',str(path),'-map','0:v:0','-map','0:a:0','-f','null','-','-progress','pipe:1','-nostats'],capture_output=True,text=True,check=True)
        assert not decoded.stderr.strip(),decoded.stderr
        counts=re.findall(r'^frame=(\d+)$',decoded.stdout,re.M)
        assert counts and int(counts[-1])==duration*30,(name,counts[-1:])
        media[name]={'decoded_frames':int(counts[-1]),'duration_seconds':duration,'resolution':[1920,1080],'fps':30,'decode':'PASS'}
        tail=subprocess.run([ff,'-v','error','-sseof','-12','-i',str(path),'-map','0:a:0',
            '-f','f32le','-acodec','pcm_f32le','-ac','2','-ar','48000','pipe:1'],
            capture_output=True,check=True)
        assert not tail.stderr.strip(),tail.stderr
        audio=np.frombuffer(tail.stdout,dtype='<f4').reshape(-1,2)
        assert 11.9<=len(audio)/48000<=12.1,(name,len(audio))
        opening_rms=float(np.sqrt(np.mean(audio[:48000]**2)))
        closing_rms=float(np.sqrt(np.mean(audio[-4800:]**2)))
        assert opening_rms>0 and 0<=closing_rms<opening_rms/10,(name,opening_rms,closing_rms)
        media[name]['audio_tail']={'decoded_seconds':len(audio)/48000,
            'first_second_rms':opening_rms,'last_tenth_second_rms':closing_rms,'fade':'PASS'}

    missing=[]; checked=0
    for name,a,b in SHOTS:
        if name in DIAGRAMS: continue
        for frame in range(a*30,b*30):
            p=out/'frames'/f'{frame:06d}.png'
            if not p.exists(): missing.append(frame); continue
            with Image.open(p) as im:
                assert im.size==(1920,1080); im.verify()
            checked+=1
    assert not missing,missing[:20]
    # Typographic layout is a display check, independent of geometric predicates.
    draw=ImageDraw.Draw(Image.new('RGB',(1920,1080)))
    for cue in CAPTIONS:
        for line in cue['text'].splitlines(): assert draw.textlength(line,font=font(48))<=1680,(cue['id'],line)
    for t in range(DURATION):
        kicker,title,label=labels(t)
        assert draw.textlength(title,font=font(54,True))<=1680,(t,title)
        assert draw.textlength(label,font=font(28))<=1680,(t,label)
    scheduled_text='\n'.join(' '.join(labels(t)) for t in range(DURATION))+'\n'+'\n'.join(c['text'] for c in CAPTIONS)
    required=['Chair44 (R44) — true geometry','uniform magnification, no height exaggeration',
        'Feature removal illustration','Plain chair — features removed',
        'True proportions — magnified section','Exploded assembly illustration',
        'finite view','Coarsening diagram — surfaces re-standardized','Hypothetical period',
        'Separated mirror copies','a nonzero slide']
    for label in required: assert label.lower() in scheduled_text.lower(),label
    for i,(x,y,copy,size,colour,bold) in enumerate(END_CARD_LINES):
        box=draw.textbbox((x,y),copy,font=(serif_font if i==0 else font)(size,bold),anchor='mm')
        assert 120<=box[0]<box[2]<=1800 and 240<=box[1]<box[3]<875,(copy,box)
    from deliver import CUTS
    for _,_,caption in CUTS:
        assert draw.textlength(caption,font=font(48))<=1680,caption
    manifest=json.loads((out/'manifest.json').read_text())
    for name,entry in manifest['outputs'].items():
        assert Path(name).name==name and name in {'r44_captioned.mp4','r44_clean.mp4','r44_teaser_40s.mp4','thumbnail.jpg','r44.srt'}
        assert hashlib.file_digest((out/name).open('rb'),'sha256').hexdigest()==entry['sha256']
    for name,digest in manifest['production_sources'].items():
        assert hashlib.file_digest((HERE/name).open('rb'),'sha256').hexdigest()==digest,name
    assert (out/'r44.srt').read_bytes()==(HERE/'CAPTIONS.srt').read_bytes()
    checks={'canonical_digests':'PASS','render_data_digest':'PASS','caption_timing_and_layout':'PASS',
        'native_3d_source_frames_verified':checked,'movies':media,'delivery_file_digests':'PASS','production_source_digests':'PASS',
        'end_card_and_teaser_layout':'PASS',
        'required_context_labels_scheduled':'PASS',
        'scope':'Technical delivery checks; visual review and mathematical theorem scope are recorded separately.'}
    (HERE/'DELIVERY_CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(checks,indent=2))
if __name__=='__main__': main()
