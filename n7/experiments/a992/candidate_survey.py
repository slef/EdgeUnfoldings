import json,random,numpy as np,itertools as it
from n7.a992 import sample,valid,points_from_parameters,unfold,penetration
from pathlib import Path
root=Path('n7/results');r=next(r for r in json.loads((root/'catalogue.json').read_text())['graphs'] if r['atlas_index']==992)
unique={}
for c in r['cofacial_candidates']:
 key=tuple(map(tuple,c['cut']))
 if key not in unique or len(c['audit']['unresolved'])<len(unique[key]['audit']['unresolved']):unique[key]=c
cs=list(unique.values());fail=[0]*len(cs);worst=[None]*len(cs);patterns={};rng=random.Random(998);samples=[];attempts=0
for d in json.loads((root/'a992-survey.json').read_text())['failures']:samples.append(d['parameters'])
while len(samples)<1200 and attempts<100000:
 attempts+=1;q=sample(rng);p=points_from_parameters(q)
 if valid(p):samples.append(q)
for q in samples:
 p=points_from_parameters(q);ss=[]
 for i,c in enumerate(cs):
  net=unfold(p,c['cut']);score=max(penetration(net[a['faces'][0]],net[a['faces'][1]]) for a in c['audit']['unresolved'])/max(1,np.ptp(p,axis=0).max());ss.append(score)
  if score>1e-8:fail[i]+=1
  if worst[i] is None or score>worst[i]['score']:worst[i]={'score':score,'parameters':q}
 key=tuple(i for i,s in enumerate(ss) if s>1e-8);patterns[key]=patterns.get(key,0)+1
print('samples',len(samples),'attempts',attempts)
for i,c in enumerate(cs):print(i,'source',c['source'],'fails',fail[i],'max',worst[i]['score'],'cut',c['cut'])
cover=[]
for k in range(1,5):
 for comb in it.combinations(range(len(cs)),k):
  if all(not set(comb)<=set(p) for p in patterns):cover.append(comb)
 if cover:break
print('smallest observed covers',cover[:20])
(root/'a992-candidate-survey.json').write_text(json.dumps({'scope':'Numerical search only. A covering candidate list here is not a proof.', 'valid':len(samples),'attempts':attempts,'candidates':cs,'failure_counts':fail,'worst':worst,'observed_covers':cover,'patterns':[{'failing_candidates':list(k),'count':v} for k,v in patterns.items()]},indent=2)+'\n')
