"""Stress the sharp-4 / inward-at-6 corner missed by the first sampler.

Numerical discovery only. A five-vertex pyramid is extended to the prescribed
seven-vertex graph by two small, outward base points.
"""
from n7.a992 import points_from_parameters,unfold,penetration,valid,T
import random,json,numpy as np
from pathlib import Path
SMALL=((0,3,2,4),(0,3,6),(0,4,6),(2,4,6),(2,3,6))
R=((0,3),(0,4),(0,6),(1,3),(2,3),(3,5))
rng=random.Random(4096);failures=[];best=None;valid_extensions=0
for k in range(14000):
    x6=-10**rng.uniform(-1,1.7);y6=10**rng.uniform(-2,1)
    X=-10**rng.uniform(-1,1.7);Y=rng.uniform(-5,5);Z=10**rng.uniform(-3,1)
    a=1+10**rng.uniform(-1,2);b=10**rng.uniform(-2,1)
    q=[x6,y6,0,0,0,0,X,Y,Z,a,b];p=points_from_parameters(q)
    try:net=unfold(p,((0,3),(0,4),(2,3),(3,6)),faces=SMALL,root=3)
    except (ValueError,FloatingPointError):continue
    scale=max(1,np.ptp(p[[0,2,3,4,6]],axis=0).max());left=penetration(net[0],net[1])/scale
    if left<1e-7:continue
    for eps in [1e-2,1e-3,1e-4,1e-5]:
        C=np.array([x6,y6]);n=np.array([-y6,x6]);v5=C/3+eps*n;v1=2*C/3+eps*n
        q[2:6]=[float(v1[0]),float(v1[1]),float(v5[0]),float(v5[1])];p=points_from_parameters(q)
        if not valid(p):continue
        valid_extensions+=1;right=unfold(p,R);scores=[penetration(right[1],right[i])/scale for i in [0,3,6]]
        row={'parameters':q.copy(),'Left':left,'Right_pairs_0_3_6':scores,'extension_epsilon':eps}
        failures.append(row)
        if best is None or min(left,max(scores))>min(best['Left'],max(best['Right_pairs_0_3_6'])):best=row
        if max(scores)>1e-6:print('JOINT',row,flush=True)
        break
    if best and min(best['Left'],max(best['Right_pairs_0_3_6']))>1e-5:break
result={'scope':'Floating discovery only; no certified signs or universal claims.','attempted':k+1,'left_failures_extended':valid_extensions,'best':best,'failures':failures}
Path('n7/results/a992-local-corner-search.json').write_text(json.dumps(result,indent=2)+'\n')
print('attempted',k+1,'extended',valid_extensions,'best',best,flush=True)
