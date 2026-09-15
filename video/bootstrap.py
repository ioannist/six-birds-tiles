#!/usr/bin/env python3
"""Install the pinned, user-local video toolchain. No sudo or system changes."""
import hashlib
from pathlib import Path
import subprocess
import sys
import tarfile
import urllib.request
import venv
HERE=Path(__file__).resolve().parent
VERSION='4.5.13'
SHA256='da4e69b06b75b9e642d106496c50e7e240218b411d2f6e18271c1d1d819cef91'
def main():
    local=HERE/'.tools'; local.mkdir(exist_ok=True)
    name=f'blender-{VERSION}-linux-x64'; archive=local/(name+'.tar.xz')
    if not archive.exists():
        tmp=archive.with_suffix('.download')
        urllib.request.urlretrieve(f'https://download.blender.org/release/Blender4.5/{name}.tar.xz',tmp)
        tmp.rename(archive)
    actual=hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()
    if actual!=SHA256: raise RuntimeError('Blender download digest mismatch')
    if not (local/name/'blender').exists():
        with tarfile.open(archive) as f: f.extractall(local,filter='data')
    if not (HERE/'.venv/bin/python').exists(): venv.create(HERE/'.venv',with_pip=True)
    subprocess.run([str(HERE/'.venv/bin/python'),'-m','pip','install','-r',str(HERE/'requirements.txt')],check=True)
    if not Path('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf').exists():
        raise RuntimeError('Install the DejaVu Sans fonts for typography, then rerun.')
    print('Toolchain ready. Source data remains pinned separately in video/source_pin.json.')
if __name__=='__main__': main()
