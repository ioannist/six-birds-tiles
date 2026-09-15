#!/usr/bin/env python3
"""Replay calibration checks. Add --enumerate for the expensive full atlas run."""
from pathlib import Path
import argparse,os,subprocess,sys
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--enumerate',action='store_true')
parser.add_argument('--list',action='store_true',help='list commands without running')
args=parser.parse_args()
scripts=[
 'r001_chair_control/compute.py','r001_chair_control/verify.py',
 'r002_frozen_maps/compute.py','r002_frozen_maps/verify.py',
 'r003_hat_reconstruction/geometry.py','r003_hat_reconstruction/independent_neighbours.py',
 'r003_hat_reconstruction/check_holes.py','r003_hat_reconstruction/check_recognition.py',
 'r005_exact_hierarchy/construct.py','r005_exact_hierarchy/growth.py',
 'r006_finite_ambiguity/control.py']
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
for script in scripts:
 path=ROOT/'rounds'/script;assert path.is_file()
 if script.endswith('/check_recognition.py') and args.enumerate:
  source=ROOT/'sources/validate/surround.py';print('FULL ENUMERATION:',source,flush=True)
  if not args.list:
   folder=ROOT/'rounds/r003_hat_reconstruction'
   with (folder/'regenerated_2patches.txt').open('w') as out,(folder/'enumeration.log').open('w') as err:
    subprocess.run([sys.executable,str(source)],stdout=out,stderr=err,env=env,check=True)
 print(script,flush=True)
 if not args.list:subprocess.run([sys.executable,str(path)],env=env,check=True)
formal=ROOT/'rounds/r004_varying_geometry_tower/formal'
print('Lean:',formal/'Tower.lean',flush=True)
if not args.list:subprocess.run(['lean','Tower.lean'],cwd=formal,env=env,check=True)
