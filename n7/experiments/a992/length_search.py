import json,random,numpy as np
from scipy.optimize import differential_evolution
from n7.a992 import *
R=((0,3),(0,4),(0,6),(1,3),(2,3),(3,5))
bounds=[(-10,10),(.001,15),(-10,10),(.001,15),(-10,10),(.001,15),(-10,10),(-10,10),(.0001,15),(.001,10),(.001,10)]
rng=random.Random(2772);pop=[]
while len(pop)<150:
 q=sample(rng)
 if valid(points_from_parameters(q)):pop.append(q)
rows=[]
for which,pair in [(0,(0,1)),(1,(0,1)),(1,(1,6)),(1,(1,3))]:
 def objective(q):
  p=points_from_parameters(q)
  if not valid(p):return 1
  l0=np.dot(p[0]-p[6],p[0]-p[6]);l3=np.dot(p[3]-p[6],p[3]-p[6]);chosen=0 if l0>=l3 else 1
  if chosen!=which:return .5+min(.4,abs(l0-l3)/max(l0,l3))
  net=unfold(p,T if which==0 else R)
  return -penetration(net[pair[0]],net[pair[1]])/max(1,np.ptp(p,axis=0).max())
 opt=differential_evolution(objective,bounds,init=np.array(pop),maxiter=140,tol=1e-10,polish=False,seed=773+which+pair[1])
 row={'choice':which,'pair':pair,'normalized_penetration':-opt.fun,'parameters':opt.x.tolist()};rows.append(row);print(row,flush=True)
open('n7/results/a992-length-rule-search.json','w').write(json.dumps({'scope':'Numerical stress testing only.','results':rows},indent=2)+'\n')
