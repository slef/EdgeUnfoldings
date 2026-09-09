"""Direct parameterization and numerical probe for the two-pair prism net.

Parameters (x,y,u,v,w,A,B,C,D) describe six vertices with their two original
quadrilateral facets intact. Numerical output is exploration, never a proof.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time
import numpy as np
from n6.families import PRISM_FACES as FACES, PRISM_CUTS as CUTS

HINGES = ((2,0),(2,1),(2,4),(4,3),(4,5))
PAIRS = ((0,5),(1,3))


def points(params):
    x,y,u,v,w,A,B,C,D = params
    a=np.array([1.,0.,0.]); b=np.array([x,y,0.]); c=np.zeros(3)
    cp=np.array([u,v,w])
    return np.array([a,b,c,A*a+B*cp,C*b+D*cp,cp])


def parameter_domain(q):
    _,y,_,_,w,A,B,C,D=q
    return min(y,w,A,B,C,D)>0 and A+B>1 and C+D>1 and D*(A-1)>B*(C-1)


def develop(p, faces=FACES, hinges=HINGES, root=2):
    """Numerical isometric development, retaining complete polygonal faces."""
    p=np.asarray(p,dtype=float)
    placed={}; a,b=faces[root][:2]
    e=p[b]-p[a]; ell=np.linalg.norm(e); ex=e/ell
    N=np.cross(e,p[faces[root][2]]-p[a]); N/=np.linalg.norm(N)
    ey=np.cross(N,ex)
    placed[root]={v:np.array([(p[v]-p[a])@ex,(p[v]-p[a])@ey]) for v in faces[root]}
    adj={i:[] for i in range(len(faces))}
    for a,b in hinges:adj[a].append(b);adj[b].append(a)
    todo=[root]
    for par in todo:
        for ch in adj[par]:
            if ch in placed:continue
            f=faces[ch];old=placed[par]
            a,b=next((a,b) for a,b in zip(f,f[1:]+f[:1]) if a in old and b in old)
            e=p[b]-p[a];s=e@e;U=old[b]-old[a];JU=np.array([-U[1],U[0]])
            N=np.cross(p[f[1]]-p[f[0]],p[f[2]]-p[f[0]]);N/=np.linalg.norm(N)
            placed[ch]={v:old[a]+((e@(p[v]-p[a]))*U+(N@np.cross(e,p[v]-p[a]))*JU)/s for v in f}
            todo.append(ch)
    return [np.array([placed[i][v] for v in f]) for i,f in enumerate(faces)]


def pair_score(a,b):
    """Positive means numerical interior overlap; negative means separation."""
    scores=[]
    for X,Y in ((a,b),(b,a)):
        for u,v in zip(X,np.roll(X,-1,axis=0)):
            e=v-u
            scores.append(np.max(e[0]*(Y-u)[:,1]-e[1]*(Y-u)[:,0])/np.linalg.norm(e))
    return min(scores)


def evaluate(params):
    if not parameter_domain(params):return None
    p=points(params)
    scale=np.max(np.linalg.norm(p[:,None]-p[None],axis=2))
    p/=scale
    # Reject unresolved nearly merged facets in this floating-point probe.
    for f in FACES:
        a,b,c=p[list(f[:3])];N=np.cross(b-a,c-a);h=np.linalg.norm(N)
        if h<1e-13:return None
        if max((p[i]-a)@N/h for i in range(6) if i not in f)>-1e-11:return None
    net=develop(p)
    return [float(pair_score(net[a],net[b])) for a,b in PAIRS]


def run(samples=10000,seed=6090901,seconds=300):
    rng=np.random.default_rng(seed);start=time.monotonic();count=tries=0
    best=[None,None];maxima=[-float('inf')]*2
    while count<samples and time.monotonic()-start<seconds:
        tries+=1
        # Broad basis distortion and ratios, while preserving facet equations.
        x,u,v=rng.normal(size=3)*10**rng.uniform(-2,2,size=3)
        y,w=10**rng.uniform(-2,2,size=2)
        A,B,C,D=10**rng.uniform(-2,2,size=4)
        q=np.array([x,y,u,v,w,A,B,C,D])
        scores=evaluate(q)
        if scores is None:continue
        count+=1
        for i,score in enumerate(scores):
            if score>maxima[i]:maxima[i]=score;best[i]=q.tolist()
        if max(scores)>1e-7:
            break
        if count%1000==0:print(count,maxima,flush=True)
    return dict(scope='Numerical exploration only; positive scores require exact verification.',
                samples=count,attempts=tries,seed=seed,seconds=time.monotonic()-start,
                status='candidate_failure' if max(maxima)>1e-7 else 'no_failure_found',
                pairs=PAIRS,maxima=maxima,parameters=best,cuts=CUTS)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples',type=int,default=10000)
    ap.add_argument('--seed',type=int,default=6090901)
    ap.add_argument('--seconds',type=float,default=300)
    ap.add_argument('--output',type=Path,default=Path('n6/results/prism-diagonal-probe.json'))
    args=ap.parse_args()
    if min(args.samples,args.seconds)<=0:ap.error('limits must be positive')
    result=run(args.samples,args.seed,args.seconds)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
