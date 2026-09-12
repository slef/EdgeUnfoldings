"""Floating discovery for the shortest-patch edge replacement lemmas."""
import json,random,time,math,itertools
from pathlib import Path
import numpy as np
from n7_pair_class_search import measurements,sample
from n7.a992 import unfold,penetration
from n7.bipyramid_morph import FACES
from n7_two_gap_wide_search import cut
PI=math.pi

def data(p,m):
 a=np.array(m['angles']);cs=[]
 for i,c in enumerate(m['pattern']):
  if c!='C':continue
  j=(i+1)%5;L=np.linalg.norm(p[j]-p[i]);r=[np.linalg.norm(p[s]-p[i]) for s in(5,6)];z=[np.linalg.norm(p[s]-p[j]) for s in(5,6)]
  x=[(rr*rr-ss*ss+L*L)/(2*L) for rr,ss in zip(r,z)];h=[math.sqrt(max(0,rr*rr-xx*xx)) for rr,xx in zip(r,x)];pp=np.array([x[0],h[0]]);qq=np.array([x[1],-h[1]]);D=np.linalg.norm(pp-qq)
  def ang(v,w):return math.atan2(abs(v[0]*w[1]-v[1]*w[0]),v@w)
  halves={}
  for fan,O,Q in((5,pp,qq),(6,qq,pp)):
   halves[fan]=[]
   for endpoint,U in((i,np.array([0.,0.])),(j,np.array([L,0.]))):
    alpha=ang(Q-O,U-O);beta=ang(O-Q,U-Q);gamma=PI-alpha-beta;radius=np.linalg.norm(U-O);gap=m['curvatures'][fan]
    radial=gamma>=PI/2+1e-8
    whole=gap>=alpha+1e-8 and beta<PI/2-1e-8 and radius*math.cos(gap-alpha)<D-1e-8*D
    halves[fan].append({'slit':endpoint,'alpha':alpha,'beta':beta,'gamma':gamma,'radius':radius,'gap':gap,'radial':radial,'empty_wedge':whole,'twice_half_gate':gap>2*alpha and beta<PI/2})
  cs.append({'patch':i,'D':D,'halves':halves})
 return min(cs,key=lambda r:r['D'])

def main():
 rng=random.Random(913620);start=time.time();valid=0;counts={};examples={};failures=[];uncovered=[];four_fail=[]
 for attempt in range(250000):
  p=sample(rng);m=measurements(p)
  if m is None or min(m['curvatures'])<1e-7:continue
  valid+=1;d=data(p,m);bad=5-m['pattern'].count('C');eligible=[(fan,h) for fan in(5,6) for h in d['halves'][fan] if h['radial'] or h['empty_wedge']]
  key=f'{bad} bad: '+('proved test' if eligible else 'not covered');counts[key]=counts.get(key,0)+1
  if key not in examples:examples[key]={'points':p.tolist(),**m,'shortest_patch':d}
  choices=eligible if eligible else [(fan,h) for fan in(5,6) for h in d['halves'][fan]]
  check_now=key not in {x.get('checked_key') for x in examples.values()} or bad>=3
  if not check_now:continue
  scores=[]
  for fan,h in choices:
   net=unfold(p,cut(fan,h['slit']),FACES,0);k=d['patch'];target={k,5+k};pairs=[(i,j) for i,j in itertools.combinations(range(10),2) if i in target or j in target]
   score=max(penetration(net[i],net[j]) for i,j in pairs)/np.ptp(p,axis=0).max();scores.append(score)
   if eligible and score>1e-7:
    failures.append({'points':p.tolist(),**m,'shortest_patch':d,'fan':fan,'choice':h,'normalized_penetration':score});print('FAILED PROVED TEST',attempt,score,flush=True);break
  examples[key]['checked_key']=key
  if failures:break
  if not eligible and len(uncovered)<10:uncovered.append({'points':p.tolist(),**m,'shortest_patch':d,'four_scores':scores})
  if not eligible and min(scores)>1e-7:
   four_fail.append({'points':p.tolist(),**m,'shortest_patch':d,'four_scores':scores});print('FOUR CANDIDATES FAIL',attempt,min(scores),flush=True)
   if len(four_fail)>=3:break
  if attempt%10000==0:print(attempt,valid,counts,len(four_fail),flush=True)
  if time.time()-start>540:break
 out={'scope':'Floating discovery and stress check only. The written shortest-patch replacement lemmas and subsequent exact examples have separate proof status.','seed':913620,'attempts':attempt+1,'valid':valid,'counts':counts,'examples':examples,'proved_test_failures':failures,'uncovered_examples':uncovered,'four_candidate_failures':four_fail}
 Path('/private/tmp/n7_star_patch_search.json').write_text(json.dumps(out,indent=2,default=lambda x:x.item())+'\n');print('DONE',attempt+1,valid,counts,'proved failures',len(failures),'four candidate failures',len(four_fail),flush=True)
if __name__=='__main__':main()
