import json, random, itertools
import numpy as np
from scipy.optimize import differential_evolution
from n7.a992 import *
V=((0,3),(0,4),(1,5),(1,6),(2,4),(4,6))
rng=random.Random(1050);pop=[]
while len(pop)<150:
 q=sample(rng)
 if valid(points_from_parameters(q)):pop.append(q)
res=[]
for pair in [(0,2),(5,1),(5,2),(5,4)]:
 best=[0,None];good=[0]
 def fun(q):
  p=points_from_parameters(q)
  if not valid(p):return 1
  good[0]+=1
  net=unfold(p,V);s=penetration(net[pair[0]],net[pair[1]])/max(1,np.ptp(p,axis=0).max())
  if s>best[0]:best[:]=[s,q.tolist()]
  return -s
 opt=differential_evolution(fun,[(-10,10),(.001,15),(-10,10),(.001,15),(-10,10),(.001,15),(-10,10),(-10,10),(.0001,15),(.001,10),(.001,10)],init=np.array(pop),maxiter=120,popsize=10,tol=1e-9,polish=False,seed=992+pair[1],workers=1)
 row={'pair':pair,'best_penetration':-opt.fun,'parameters':opt.x.tolist(),'positive_seen':best,'valid_evaluations':good[0]};res.append(row);print(row,flush=True)
open('n7/results/a992-alternative-search.json','w').write(json.dumps({'scope':'Targeted numerical optimization, not a proof.','results':res},indent=2)+'\n')
