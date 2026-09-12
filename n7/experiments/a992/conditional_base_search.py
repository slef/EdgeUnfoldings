"""Freeze a discovered Left obstruction and vary only the two other base vertices.

This conditions on the proved localization lemma. Floating signs are discovery
filters, never certificates. Negative best scores do not prove the repair rule.
"""
import json
import random
from pathlib import Path
import numpy as np
from n7.a992 import points_from_parameters, valid, unfold, penetration

ROOT=Path(__file__).resolve().parents[2]
R=((0,3),(0,4),(0,6),(1,3),(2,3),(3,5))

def run(trials=350, seed=12881):
    rng=random.Random(seed)
    sources=[]
    for name in ('a992-survey.json','a992-local-corner-search.json'):
        rows=json.loads((ROOT/'results'/name).read_text())['failures']
        sources.extend((name,i,r['parameters']) for i,r in enumerate(rows))
    total=0;by_source=[];suspects=[]
    for name,i,q0 in sources:
        q0=list(q0);C=np.array(q0[:2]);N=np.array([-C[1],C[0]])
        norm=float(C@C)
        t1=float(np.array(q0[2:4])@C/norm);h1=float(np.array(q0[2:4])@N/norm)
        t5=float(np.array(q0[4:6])@C/norm);h5=float(np.array(q0[4:6])@N/norm)
        seen=0;best=None
        for k in range(trials):
            if k%2:
                t,tt=sorted([rng.uniform(-1,2),rng.uniform(-1,2)],reverse=True)
                h,hh=10**rng.uniform(-7,1),10**rng.uniform(-7,1)
            else:
                span=10**rng.uniform(-3,.4)
                t,tt=t1+rng.uniform(-span,span),t5+rng.uniform(-span,span)
                h,hh=h1*10**rng.uniform(-2,2),h5*10**rng.uniform(-2,2)
            q=q0.copy();q[2:4]=(t*C+h*N).tolist();q[4:6]=(tt*C+hh*N).tolist()
            p=points_from_parameters(q)
            if not valid(p):continue
            seen+=1;total+=1
            left=unfold(p);lp=penetration(left[0],left[1])
            net=unfold(p,R);scale=max(1.,float(np.ptp(p,axis=0).max()))
            scores=[penetration(net[1],net[j])/scale for j in (0,3,6)]
            row={'parameters':q,'left_score':lp/scale,'right_scores_0_3_6':scores}
            if best is None or max(scores)>max(best['right_scores_0_3_6']):best=row
            if min(lp/scale,max(scores))>1e-8:suspects.append(row)
        by_source.append({'file':name,'index':i,'valid_extensions':seen,'best':best})
        if i%40==0:print(name,i,'valid',total,'floating joint failures',len(suspects),flush=True)
    return {'scope':'Numerical conditional search; no exact signs or universal conclusion.',
            'seed':seed,'trials_per_source':trials,'sources':len(sources),'valid':total,
            'suspected_joint_failures':suspects,'by_source':by_source}

if __name__=='__main__':
    result=run()
    (ROOT/'results/a992-conditional-base-search.json').write_text(json.dumps(result,indent=2)+'\n')
    print({k:result[k] for k in ('sources','valid')},'suspects',len(result['suspected_joint_failures']))
