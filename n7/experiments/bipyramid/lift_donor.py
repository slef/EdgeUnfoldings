import json,numpy as np
from pathlib import Path
from n7.bipyramid_product_rule import certify
from n7.bipyramid_rule_checks import patch_pattern
from n7.bipyramid_morph import exact_points,support,I
raw=json.loads(Path('/private/tmp/n6_three_product_search.json').read_text())['conflicts'][0];p=np.array(raw['points']);a,b=p[:2];e=(b-a)/np.linalg.norm(b-a)
def closest(base):
 z=[];h=[]
 for q in p[4:]:v=q-base;z.append(v@e);h.append(np.linalg.norm(v-(v@e)*e))
 return base+(h[1]*z[0]+h[0]*z[1])/(h[0]+h[1])*e
c=closest(a);g=sum((c-q)/np.linalg.norm(c-q)for q in p[4:]);g/=np.linalg.norm(g);fraction=(c-a)@e/np.linalg.norm(b-a);print('minimum edge fraction',fraction,flush=True)
rows=[]
for kind,frac in [('three-mixed-block',fraction),('four-mixed-left',fraction/2),('four-mixed-right',(1+fraction)/2)]:
 for eps in (1e-6,1e-5,1e-4,1e-3,.01):
  v=closest(a+eps*g) if kind=='three-mixed-block'else a+frac*(b-a)+eps*g
  pts=np.vstack([a,v,p[1:4],p[4:]]);row={'id':kind,'points':[[str(round(x,12))for x in v]for v in pts],'expect_both_tests_fail':True,'donor_pattern':'CBBF','edge_position':float(frac),'outward_step':eps}
  try:
   row['certificate']=certify(row);print('SUCCESS',kind,eps,row['certificate']['pattern'],row['certificate']['strictly_failed_vertices'],flush=True);rows.append(row);break
  except Exception as err:print('TRY',kind,eps,err,flush=True)
Path('/private/tmp/block-product-counterexamples.json').write_text(json.dumps({'scope':'Exact failures of the proposed common-product-pole conjecture in consecutive inward blocks. These are not counterexamples to edge unfolding.','examples':rows},indent=2)+'\n')
