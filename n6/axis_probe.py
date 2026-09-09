"""Bounded numerical searches using coordinates around the v--w axis.

All candidates require independent rational verification. Coordinate bounds,
positive guards, optimizer failures, and absence of candidates are never proofs.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path
import sys
import time
import numpy as np
from scipy.optimize import minimize
from n6.prism_diagonal import pair_score

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'durer_small_n'))
from octa import random_octahedra,sharpest_apex,Octa

FACES=[(1,2+i,2+(i+1)%4) for i in range(4)]+[(0,2+(i+1)%4,2+i) for i in range(4)]
ADJ={v:set() for v in range(6)}
for face in FACES:
    for v in face:ADJ[v].update(set(face)-{v})


def points(x):
    radius=np.exp(x[:4]);z=x[4:8];phi=np.r_[0,np.cumsum(x[8:])]
    return np.vstack(([0,0,0],[0,0,1],np.c_[radius*np.cos(phi),radius*np.sin(phi),z]))


def pack(o,slit):
    offset=int(np.argmax(o.ku))-slit;ring=np.roll(o.u,-offset)
    P=o.P-o.P[o.v];d=np.linalg.norm(P[o.w]);ez=P[o.w]/d
    ex=P[ring[0]]-ez*(ez@P[ring[0]]);ex/=np.linalg.norm(ex);ey=np.cross(ez,ex)
    Q=P[ring]@np.stack((ex,ey,ez),axis=1)/d
    radius=np.linalg.norm(Q[:,:2],axis=1);phi=np.unwrap(np.arctan2(Q[:,1],Q[:,0]));turns=np.diff(phi)
    if (turns<=0).any():raise ValueError('Wrong azimuth ring orientation')
    return np.r_[np.log(radius),Q[:,2],turns]


def quantities(x):
    P=points(x);U=P[2:];Un=np.roll(U,-1,axis=0)
    s=np.linalg.norm(U,axis=1);r=np.linalg.norm(U-P[1],axis=1);ell=np.linalg.norm(Un-U,axis=1)
    def tri(pole):
        a,b=U-pole,Un-pole;area=np.linalg.norm(np.cross(a,b),axis=1)
        nu=np.arctan2(area,np.sum(a*b,axis=1))
        av=np.arctan2(area,np.sum((pole-U)*(Un-U),axis=1))
        return nu,av,np.pi-nu-av
    nu,av,ap=tri(P[0]);om,bw,bp=tri(P[1])
    inc=np.array([nu,om]+[[av[i],ap[i-1],bw[i],bp[i-1]] for i in range(4)])
    total=inc.sum(axis=1);scale=np.max(np.linalg.norm(P[:,None]-P[None],axis=2));support=[]
    for face in FACES:
        a,b,c=P[list(face)];N=np.cross(b-a,c-a);N/=max(np.linalg.norm(N),1e-100)
        support.extend(-((P[j]-a)@N)/scale for j in range(6) if j not in face)
    sigma=bp[0]+bw[1];tau=bp[1]+bw[2];SW=sigma+tau
    apex=np.array([s[1]*np.sin(SW+ap[0])-ell[1]*np.sin(tau),
                   s[2]*np.sin(SW+av[2])-ell[1]*np.sin(sigma)])/scale
    far=np.array([ell[0]*np.sin(SW)-ell[1]*np.sin(tau),
                  ell[2]*np.sin(SW)-ell[1]*np.sin(sigma)])/scale
    return dict(points=P,incident=inc,totals=total,support=np.array(support),SW=SW,
                angle_target=SW+ap[0]-np.pi,apex_entry=apex,far_entry=far,scale=scale)


def run(seconds,seed,slit,objective,starts=100,guard=1e-5):
    rng=np.random.default_rng(seed);start=time.monotonic();initial=[]
    for P,faces,adj in random_octahedra(rng,starts):initial.append(pack(sharpest_apex(P,faces,adj),slit))
    best=None;records=[];attempts=0
    while time.monotonic()-start<seconds:
        x=initial[attempts%len(initial)].copy()
        if attempts>=len(initial):x[:8]+=rng.normal(size=8)*rng.uniform(.001,.1)
        @lru_cache(maxsize=128)
        def cached(t):return quantities(np.array(t))
        def data(x):
            if time.monotonic()-start>seconds:raise TimeoutError
            return cached(tuple(x))
        def constraints(x):
            q=data(x);total=q['totals'];gam=np.r_[x[8:],2*np.pi-sum(x[8:])]
            out=[gam-guard,np.pi-gam-guard,q['support']-guard,total[1:]-total[0]-guard,
                 total[[j+2 for j in range(4) if j!=slit]]-total[slit+2]-guard]
            if objective!='local':out.append(np.array([np.pi-q['SW']-guard]))
            return np.concatenate(out)
        def score(q):
            if objective=='left-angle':return -q['angle_target']
            if objective=='left-entry':return q['apex_entry'][0]
            if objective=='both-reach':return float(min(np.maximum(q['apex_entry'],q['far_entry'])))
            if objective=='both-apices':return float(min(q['apex_entry']))
            o=Octa(q['points'],0,FACES,ADJ)
            return max(pair_score(*o.pair_faces(slit,name))/q['scale'] for name in Octa.LOCAL)
        try:
            res=minimize(lambda x:-score(data(x)),x,method='SLSQP',
                         bounds=[(-6,6)]*4+[(-50,50)]*4+[(.00001,np.pi-.00001)]*3,
                         constraints=[{'type':'ineq','fun':constraints}],options={'ftol':1e-10,'maxiter':500})
            q=data(res.x);feas=float(min(constraints(res.x)));value=float(score(q))
        except TimeoutError:break
        attempts+=1
        if feas>=-1e-8 and (best is None or value>best['score']):
            best=dict(points=q['points'].tolist(),apex=0,slit_vertex=slit+2,equator=[2,3,4,5],slit_index=slit,
                      triple_index=0,score=value,angle_target=float(q['angle_target']),sum_W=float(q['SW']),
                      apex_entry=q['apex_entry'].tolist(),far_entry=q['far_entry'].tolist(),
                      minimum_constraint=feas,optimizer_success=bool(res.success),iteration=attempts)
            records.append(best);print('improvement',attempts,objective,value,flush=True)
            if value>1e-6:break
        if attempts%20==0:print('progress',attempts,round(time.monotonic()-start,1),best['score'] if best else None,flush=True)
    return dict(scope='Numerical exploration only; no certificate or universal conclusion.',seconds=time.monotonic()-start,
                seed=seed,slit_index=slit,objective=objective,coordinate_bounds='log radii [-6,6], heights [-50,50], turns (0,pi)',
                guard=guard,attempts=attempts,best=best,improvements=records)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--seconds',type=float,default=600)
    ap.add_argument('--seed',type=int,default=6090915);ap.add_argument('--slit-index',type=int,choices=(0,3),default=3)
    ap.add_argument('--objective',choices=('left-angle','left-entry','both-reach','both-apices','local'),default='both-reach')
    ap.add_argument('--starts',type=int,default=100);ap.add_argument('--guard',type=float,default=1e-5)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if min(args.seconds,args.starts,args.guard)<=0:ap.error('Limits and guard must be positive')
    report=run(args.seconds,args.seed,args.slit_index,args.objective,args.starts,args.guard)
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
