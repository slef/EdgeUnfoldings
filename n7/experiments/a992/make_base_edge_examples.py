"""Rebuild exact example records; floating clipping proposes a witness only.

Every saved sign and witness is subsequently checked with exact intervals.
"""
from fractions import Fraction as F
import json
import numpy as np
from n7.a992_exact import ROOT,T,certificate,geometry,develop
from n7.a992 import intersection_polygon
from n7.base_edge_examples import RIGHT,example_signs
rows=[]
for q in [('1.8','.2','.75','.4','-.15','.3','-1.2','1.7','1.1','.05','1.4'),
          ('1.8','.2','.8','.8','-1','.6','-1.2','1.7','1.1','.05','1.4')]:
    p,_=geometry(q);n=develop(p,T)
    polygons=[np.array([[z.mid() for z in a] for a in n[j]]) for j in (0,1)]
    w=intersection_polygon(*polygons).mean(axis=0)
    w=[F(str(round(float(z),6))) for z in w]
    c=certificate(q,T,(0,1),w,RIGHT);c['base_edge_signs']=example_signs(q);rows.append(c)
    print(c['base_edge_signs']['classification'],list(map(str,w)),flush=True)
report={'scope':'Exact examples and implementation checks only; universal proof in A992_BASE_EDGES.md.', 'examples':rows}
(ROOT/'results/a992-base-edge-examples.json').write_text(json.dumps(report,indent=2)+'\n')
