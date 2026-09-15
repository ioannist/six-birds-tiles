#!/usr/bin/env python3
"""Separate tuple arithmetic and declarative replay of the source local rules.
Rules are transcribed from matching.py / paper Section 4, not independently
discovered. Enumeration completeness and arbitrary alignment use the paper.
"""
from pathlib import Path
from collections import Counter
import json,hashlib,sys
HERE=Path(__file__).resolve().parent;SOURCE=HERE.parents[1]/'sources/validate'
I=(1,0,0,0,1,0)
def compose(A,B):
 a,b,c,d,e,f=A;g,h,i,j,k,l=B
 return (a*g+b*j,a*h+b*k,a*i+b*l+c,d*g+e*j,d*h+e*k,d*i+e*l+f)
def read(path):
 lines=iter(path.read_text().splitlines());out=[]
 for line in lines:
  p={}
  for _ in range(int(line)):
   level,coords=next(lines).split(';');A=tuple(map(int,coords.strip()[1:-1].split(',')))
   assert len(A)==6 and A not in p;p[A]=int(level)
  assert p[I]==0;out.append(p)
 return out
RULES=[('H1',[(1,1,2,0,-1,2)]),('H2',[(0,-1,4,-1,0,-2),(0,-1,8,1,1,-4)]),('H3',[(0,-1,-2,-1,0,4)]),('H4',[(1,1,-4,0,-1,2)]),('T1',[(0,-1,2,1,1,2),(1,1,6,-1,0,0)]),('P2',[(-1,0,2,0,-1,-4),(1,1,4,-1,0,-2)]),('F2',[(-1,-1,8,1,0,-4),(0,1,4,-1,-1,4)])]
def label(A,p):
 return next((kind for kind,needs in RULES if all(compose(A,B) in p for B in needs)),'FP1')
WITHIN={'H1':[((0,-1,-2,-1,0,4),['H2']),((0,-1,4,-1,0,-2),['H3']),((1,1,2,0,-1,2),['H4'])], 'H2':[((0,-1,4,-1,0,-2),['H1'])], 'H3':[((0,-1,-2,-1,0,4),['H1'])], 'H4':[((1,1,-4,0,-1,2),['H1'])], 'FP1':[((0,-1,2,1,1,2),['P2','F2'])], 'P2':[((1,1,-4,-1,0,2),['FP1'])], 'F2':[((1,1,-4,-1,0,2),['FP1'])], 'T1':[]}
# Each row: centre labels; ordered alternative contacts; allowed neighbour roles.
BETWEEN=[
 (['H2'],[((0,-1,-2,1,1,-2),['T1','P2']),((1,1,-4,-1,0,2),['T1'])]),
 (['H1'],[((-1,-1,2,0,1,-4),['T1','FP1'])]),
 (['H3'],[((1,1,-2,-1,0,-2),['T1','FP1'])]),
 (['T1'],[((0,-1,2,1,1,2),['H2'])]),
 (['T1','P2'],[((1,1,4,-1,0,-2),['H2'])]),
 (['T1','FP1'],[((1,1,-4,-1,0,2),['H3','H4'])]),
 (['F2'],[((-1,-1,8,1,0,-4),['F2'])]),
 (['F2'],[((0,1,4,-1,-1,4),['F2'])]),
 (['H2','P2','F2'],[((0,1,0,-1,-1,6),['H2','P2']),((1,0,-2,0,1,4),['H3','H4','FP1','F2'])]),
 (['H3','H4','FP1'],[((-1,-1,8,1,0,-4),['H2','P2']),((0,1,6,-1,-1,0),['H3','H4','FP1','F2'])]),
 (['H2','P2'],[((-1,-1,6,1,0,0),['H2','F2','P2']),((0,1,4,-1,-1,4),['H3','H4','FP1'])]),
 (['H3','H4','FP1','F2'],[((1,0,2,0,1,-4),['H2','F2','P2']),((-1,-1,6,1,0,-6),['H3','H4','FP1'])]),
 (['P2'],[((-1,0,10,0,-1,-2),['P2']),((1,1,6,-1,0,0),['FP1','F2'])]),
 (['FP1','F2'],[((0,-1,0,1,1,-6),['P2']),((-1,0,2,0,-1,-4),['FP1','F2'])])]
def check(p):
 labs={A:label(A,p) for A,n in p.items() if n<2};kind=labs[I]
 for A,allowed in WITHIN[kind]:assert labs[A] in allowed
 count=0
 for kinds,options in BETWEEN:
  if kind not in kinds:continue
  found=next(((A,allowed) for A,allowed in options if A in p),None)
  assert found is not None;A,allowed=found;assert labs[A] in allowed;count+=1
 # Geometric definitions use relative transforms, hence commute with a change
 # of global frame. Test both rotation and reflection on every local example.
 for G in ((0,-1,14,1,1,-8),(1,1,6,0,-1,0)):
  moved={compose(G,A):n for A,n in p.items()}
  assert all(label(compose(G,A),moved)==k for A,k in labs.items())
 return kind,len(labs),count
def main():
 original=read(SOURCE/'2patches.txt');regen=read(HERE/'regenerated_2patches.txt')
 canonical=lambda ps:{tuple(sorted(p.items())) for p in ps}
 assert len(original)==len(regen)==len(canonical(original))==len(canonical(regen))==188
 assert canonical(original)==canonical(regen)
 checks=[check(p) for p in regen]
 # Also replay the author's complete matcher; no unchecked printed PASS count.
 sys.path.insert(0,str(SOURCE));import matching
 import surround
 neighbours=json.loads((HERE/'neighbours_independent.json').read_text())['placements']
 assert {tuple(x.m) for x in surround.getLegalNeighbours()}=={tuple(x['matrix']) for x in neighbours if not x['holes']}
 assert {tuple(x.m) for x in surround.getLegalNeighbours(True)}=={tuple(x['matrix']) for x in neighbours}
 with (HERE/'regenerated_2patches.txt').open() as f:auth=matching.readPatches(f)
 assert all(matching.processPatch(p) for p in auth)
 out={'status':'PASS','patches':len(regen),'matches_reference_as_sets':True,'root_role_counts':dict(Counter(k for k,_,_ in checks)),'labelled_tiles':sum(n for _,n,_ in checks),'between_checks':sum(n for _,_,n in checks),'author_matcher_passes':len(auth),'scope':'separate arithmetic/declarative rule replay and frame-covariance tests; source enumeration replay is not a separately proved completeness theorem','hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [SOURCE/'2patches.txt',SOURCE/'matching.py',HERE/'regenerated_2patches.txt']}}
 (HERE/'recognition.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
