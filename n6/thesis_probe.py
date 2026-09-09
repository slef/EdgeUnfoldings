"""Numerical audit of the octahedral last-face move in DiBiase Chapter 3.

The labels reconstruct Figure 3.28's cyclic three-arm core. They are explicit
here because a figure-specific claim must not silently become a universal lemma.
This script proposes integer-coordinate candidates; polycert checks them exactly.
"""
import argparse
import itertools
import json
from pathlib import Path
import sys
import time
import numpy as np
from n6.prism_diagonal import develop,pair_score

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'durer_small_n'))
from octa import octa_structure

NAMES=('root','A','B','C','D','E','F','G')
FACES=((0,1,2),(0,3,1),(1,5,2),(0,2,4),(1,3,5),(2,5,4),(0,4,3),(3,4,5))
CORE=((0,1),(0,2),(0,3),(1,4),(2,5),(3,6))


def cuts(parent):
    hinges=CORE+((parent,7),)
    uncut={frozenset(FACES[a])&frozenset(FACES[b]) for a,b in hinges}
    edges={frozenset((a,b)) for f in FACES for a,b in zip(f,f[1:]+f[:1])}
    return [sorted(e) for e in sorted(edges-uncut,key=lambda x:sorted(x))]


def relabel(P,structure,root):
    fs,adj=structure;a,b,c=root
    opp={v:next(w for w in range(6) if w!=v and w not in adj[v]) for v in range(6)}
    return P[[a,b,c,opp[c],opp[b],opp[a]]]


def overlaps(net,pairs):
    return [(a,b,float(pair_score(net[a],net[b]))) for a,b in pairs if pair_score(net[a],net[b])>1e-7]


def run(samples=10000,seconds=600,seed=6090902):
    rng=np.random.default_rng(seed);start=time.monotonic();count=tries=0;found={}
    core_failures=all_move_failures=0
    while count<samples and time.monotonic()-start<seconds:
        tries+=1;P=rng.integers(-10,11,size=(6,3))
        st=octa_structure(P)
        if st is None:continue
        # Every returned facet is oriented outward. The six labels then match FACES.
        P=relabel(P,st,st[0][int(rng.integers(8))]);scale=np.max(np.linalg.norm(P[:,None]-P[None],axis=2))
        nets={parent:develop(P/scale,FACES,CORE+((parent,7),),root=0) for parent in (4,5,6)}
        core=overlaps(nets[4],itertools.combinations(range(7),2))
        moves={parent:overlaps(net,[(i,7) for i in range(7)]) for parent,net in nets.items()}
        acute=np.dot(P[4]-P[3],P[5]-P[3])>0
        ag=next((s for a,b,s in moves[6] if a==1),None)
        record=dict(points=P.tolist(),core_overlaps=core,move_overlaps=moves,
                    alpha4_acute=bool(acute),alpha4_dot=int(np.dot(P[4]-P[3],P[5]-P[3])))
        if ag is not None and acute and 'acute_A_G' not in found:found['acute_A_G']=record
        if ag is not None and moves[5] and not core and 'move_to_E_not_safe' not in found:found['move_to_E_not_safe']=record
        if core:
            core_failures+=1
            if 'core_overlap' not in found:found['core_overlap']=record
        if not core and all(moves.values()):
            all_move_failures+=1
            if 'all_three_moves_fail' not in found:found['all_three_moves_fail']=record
        count+=1
        if count%1000==0:print(count,core_failures,all_move_failures,list(found),flush=True)
    return dict(scope='Numerical audit candidates only; label reconstruction and exact verification are separate obligations.',
                samples=count,attempts=tries,seed=seed,seconds=time.monotonic()-start,
                core_failures=core_failures,all_move_failures=all_move_failures,found=found,
                faces=FACES,face_names=NAMES,core_hinges=CORE)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples',type=int,default=10000);ap.add_argument('--seconds',type=float,default=600)
    ap.add_argument('--seed',type=int,default=6090902)
    ap.add_argument('--output',type=Path,default=Path('n6/results/thesis-probe.json'))
    args=ap.parse_args();result=run(args.samples,args.seconds,args.seed)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
