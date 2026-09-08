"""Numerical differential check of the proved cone and apex formulas.

This tests implementation conventions. The mathematical arguments are in
CASE_PARTITION.md; sampled formula checks are not proofs of unfolding.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time
import numpy as np
from n6.prism_diagonal import pair_score

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'durer_small_n'))
from octa import random_octahedra,all_apexes


def run(samples,seed):
    rng=np.random.default_rng(seed);counts=Counter();errors=Counter();bad=[];start=time.monotonic()
    for P,faces,adj in random_octahedra(rng,samples):
        for o in all_apexes(P,faces,adj):
            # A numerical stability filter, not an omitted case in the proof.
            if min(o.r.min(),o.s.min(),o.l.min())/o.scale<.001 or min(o.kappa.values())<.001:continue
            for i in range(4):
                j,jj=(i+1)%4,(i+2)%4;k=(i-1)%4
                net=o.Z(k);left,mid,right=[net['V',x] for x in (i,j,jj)]
                u,up=mid[2],mid[1];ell=np.linalg.norm(up-u)
                ex=(up-u)/ell;ey=np.array([ex[1],-ex[0]])
                def direction(p,base):
                    d=p-base;d/=np.linalg.norm(d);return np.array([d@ex,d@ey])
                alpha=o.aV[j]+o.ku[j];beta=o.aVp[j]+o.ku[jj]
                sigma=o.bWp[i]+o.bW[j];tau=o.bWp[j]+o.bW[jj];SW=sigma+tau
                predictions=[(left[0],u,alpha),(left[2],u,2*np.pi-sigma),
                             (right[1],up,np.pi+tau),(right[0],up,3*np.pi-beta)]
                errors['maximum_direction_error']=max(errors['maximum_direction_error'],
                    max(float(np.linalg.norm(direction(p,base)-[np.cos(a),np.sin(a)])) for p,base,a in predictions))
                counts['triples']+=1
                if alpha+beta>=np.pi and SW>=np.pi:
                    counts['base_cone_excluded']+=1
                    if pair_score(left,right)/o.scale>1e-7:bad.append(dict(reason='base_cone',points=P.tolist(),apex=o.v,i=i))
                if SW>=np.pi:continue
                counts['small_SW']+=1
                def away(base,far,p):
                    d=(far-base)/np.linalg.norm(far-base)
                    cross=lambda q:d[0]*(q-base)[1]-d[1]*(q-base)[0]
                    return -np.sign(cross(np.zeros(2)))*cross(p)
                actual_left=away(up,right[1],left[0])
                actual_right=away(u,left[2],right[0])
                a,b=o.aVp[i],o.aV[jj]
                formula_left=o.s[j]*np.sin(SW+a)-ell*np.sin(tau)
                formula_right=o.s[jj]*np.sin(SW+b)-ell*np.sin(sigma)
                errors['maximum_apex_distance_error']=max(errors['maximum_apex_distance_error'],
                    abs(float(actual_left-formula_left))/o.scale,abs(float(actual_right-formula_right))/o.scale)
                # The same three-face development belongs to either slit
                # outside it: k=i-1 or k=i. Count both selected-net triples.
                if o.v==max(o.kappa,key=o.kappa.get) and int(np.argmax(o.ku)) in (k,i):
                    counts['H3R_small_SW']+=1
                    counts['H3R_left_angle_allows_entry']+=SW+a<np.pi
                    counts['H3R_right_angle_allows_entry']+=SW+b<np.pi
                    if max(actual_left,actual_right)>1e-7*o.scale:
                        bad.append(dict(reason='selected_apex_entry_candidate',points=P.tolist(),apex=o.v,i=i,
                                        slit_vertex=o.u[int(np.argmax(o.ku))],left=float(actual_left/o.scale),right=float(actual_right/o.scale)))
    return dict(scope='Numerical differential check only; no universal conclusion from sampling.',
                samples=samples,seed=seed,counts={k:int(v) for k,v in counts.items()},
                errors={k:float(v) for k,v in errors.items()},candidates=bad,seconds=time.monotonic()-start)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--samples',type=int,default=2000)
    ap.add_argument('--seed',type=int,default=6090906)
    ap.add_argument('--output',type=Path,default=Path('n6/results/partition-apex-differential.json'))
    args=ap.parse_args();result=run(args.samples,args.seed)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
