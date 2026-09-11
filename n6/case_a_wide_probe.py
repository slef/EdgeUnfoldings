"""Numerical search for failure of the wider Case A test with a low fan.

A negative sufficient-test score is not itself overlap. No count here proves
coverage or absence of counterexamples. Proposed shapes need exact replay.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
from durer_small_n.octa import random_octahedra,all_apexes
from n6.prism_diagonal import pair_score


def run(samples=150000,seed=6091263,seconds=300):
    rng=np.random.default_rng(seed);start=time.monotonic();count=casea=bad=0
    failure=worst=None;tol=1e-7
    for p,faces,adj in random_octahedra(rng,samples):
        count+=1
        for o in all_apexes(p,faces,adj):
            if o.kw>np.pi-tol or min(o.kappa.values())<tol:continue
            for i in range(4):
                j,h=(i+1)%4,(i+2)%4
                if o.ku[j]+o.ku[h]>=o.nu[j]-tol:continue
                casea+=1;theta=np.pi-o.nu[j]+o.ku[j]+o.ku[h];half=(np.pi+theta)/2
                alpha=o.aV[j]+o.ku[j];beta=o.aVp[j]+o.ku[h]
                L=o.l[j]*np.sin(beta)/np.sin(theta);R=o.l[j]*np.sin(alpha)/np.sin(theta)
                left=(L-o.s[j])/o.scale;right=(R-o.s[h])/o.scale
                slack=max(min(left,half-o.nu[i]),min(right,half-o.nu[h]))
                if worst is None or slack<worst['slack']:
                    worst=dict(points=p.tolist(),faces=faces,source=o.v,fan=o.w,ring=o.u,i=i,
                        theta=theta,half=half,left_angle=float(o.nu[i]),right_angle=float(o.nu[h]),
                        left_short=left,right_short=right,curvatures=o.kappa,slack=float(slack))
                if slack < -tol:
                    bad+=1;net=o.Z(i)
                    failure=dict(**worst,score=float(pair_score(net['V',i],net['V',h])/o.scale));break
            if failure:break
        if failure:break
        if count%10000==0:print(count,casea,'worst',worst['slack'],flush=True)
        if time.monotonic()-start>seconds:break
    return dict(scope='Numerical hypothesis test only; no universal exclusion or shape-space coverage.',
        seed=seed,sample_limit=samples,tolerance=tol,samples=count,case_A=casea,
        half_angle_failures=bad,seconds=time.monotonic()-start,worst=worst,failure=failure)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples',type=int,default=150000);ap.add_argument('--seed',type=int,default=6091263)
    ap.add_argument('--seconds',type=float,default=300);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();r=run(args.samples,args.seed,args.seconds)
    args.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k not in ('worst','failure')},indent=2))
