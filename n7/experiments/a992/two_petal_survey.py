from n7.a992 import *
import random,json,numpy as np
cuts=[T,((0,3),(0,4),(0,6),(1,3),(2,3),(3,5))]
rng=random.Random(1332);seen=0;tried=0;failures=[];joint=[];worst=[0,None]
while seen<1800 and tried<100000:
 tried+=1;q=sample(rng);p=points_from_parameters(q)
 if not valid(p):continue
 seen+=1;l0=np.linalg.norm(p[0]-p[6]);l3=np.linalg.norm(p[3]-p[6]);choice=0 if l0>=l3 else 1
 nets=[unfold(p,c) for c in cuts];scores=[max(penetration(n[1],n[i]) for i in [0,2,3,4,5,6]) for n in nets]
 if scores[choice]>1e-8:failures.append({'parameters':q,'choice':choice,'scores':scores,'lengths':[l0,l3]})
 if min(scores)>1e-8:joint.append({'parameters':q,'choice':choice,'scores':scores,'lengths':[l0,l3]})
 if min(scores)>worst[0]:worst=[min(scores),q]
print('valid',seen,'attempts',tried,'length rule fails',len(failures),'both fail',len(joint),'worst',worst,flush=True)
open('n7/results/a992-two-petal-survey.json','w').write(json.dumps({'scope':'Exploration only.','samples':seen,'attempts':tried,'length_rule_failures':failures,'joint_failures':joint,'worst':worst},indent=2)+'\n')
