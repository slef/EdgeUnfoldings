from n7.a992 import *
from scipy.optimize import differential_evolution
import json,numpy as np,random
cuts=[T,((0,3),(0,4),(0,6),(1,3),(2,3),(3,5)),((0,4),(0,6),(1,3),(2,3),(3,5),(3,6))]
cuts=cuts[:2];residuals=[[0],[0,3,6]]
rng=random.Random(5512);pop=[]
while len(pop)<180:
 q=sample(rng)
 if valid(points_from_parameters(q)):pop.append(q)
best=[-1,None,None];evaluations=[0]
def objective(q):
 p=points_from_parameters(q)
 if not valid(p):return 1
 evaluations[0]+=1;nets=[unfold(p,c) for c in cuts];scores=[max(penetration(n[1],n[i]) for i in rs) for n,rs in zip(nets,residuals)];s=min(scores)/max(1,np.ptp(p,axis=0).max())
 if s>best[0]:best[:]=[s,q.tolist(),scores]
 return -s
opt=differential_evolution(objective,[(-15,15),(.0001,20),(-15,15),(.0001,20),(-15,15),(.0001,20),(-15,15),(-15,15),(.0001,20),(.0001,15),(.0001,15)],init=np.array(pop),maxiter=160,polish=False,seed=9961,tol=1e-9)
result={'scope':'Numerical search only, not a certificate or proof.','valid_evaluations':evaluations[0],'best_minimum_penetration':best[0],'parameters':best[1],'scores':best[2]}
open('n7/results/a992-two-hinges-search.json','w').write(json.dumps(result,indent=2)+'\n');print(result,flush=True)
