"""Check an exact abstract face-angle model against the linear necessary facts.

Angles are rational multiples of pi. A passing result does not assert that a
convex polyhedron realizes these angles, or that its unfolding overlaps.
"""
from fractions import Fraction as F
from n6.certify import require


def verify(data):
    angles={name:list(map(F,row)) for name,row in data['angles'].items()}
    names={'nu','aV','aVp','om','bW','bWp'}
    require(set(angles)==names and all(len(v)==4 for v in angles.values()),'Incomplete angle assignment')
    require(all(0<x<1 for row in angles.values() for x in row),'Invalid face angle')
    for t in range(4):
        require(sum(angles[n][t] for n in ('nu','aV','aVp'))==1,'Invalid V triangle sum')
        require(sum(angles[n][t] for n in ('om','bW','bWp'))==1,'Invalid W triangle sum')
    def incident(v):
        if v=='v':return angles['nu']
        if v=='w':return angles['om']
        return [angles['aV'][v],angles['aVp'][(v-1)%4],angles['bW'][v],angles['bWp'][(v-1)%4]]
    vertices=['v','w',0,1,2,3];curvatures={}
    for v in vertices:
        row=incident(v);total=sum(row)
        require(total<2,'Nonpositive curvature')
        require(all(2*x<total for x in row),'Strict cone inequality fails')
        curvatures[v]=2-total
    k=data['slit_index'];i=data['triple_index'];j,jj=(i+1)%4,(i+2)%4
    require(k in range(4) and i in range(4),'Invalid ring index')
    require(all(curvatures['v']>curvatures[v] for v in vertices if v!='v'),'Strict apex ranking fails')
    require(all(curvatures[k]>curvatures[t] for t in range(4) if t!=k),'Strict slit ranking fails')
    SW=angles['bWp'][i]+angles['bW'][j]+angles['bWp'][j]+angles['bW'][jj]
    require(SW<1,'Not in the remaining small fan-angle regime')
    require(SW+angles['aVp'][i]<1,'Does not refute the proposed angle implication')
    return dict(result='verified_abstract_angle_countermodel',curvatures_in_pi_units={str(k):str(v) for k,v in curvatures.items()},
                fan_angle_sum_in_pi_units=str(SW),left_near_angle_plus_fan_sum_in_pi_units=str(SW+angles['aVp'][i]),
                scope='The listed linear face-angle facts, even strictly, do not imply this apex-direction bound. No geometric realization or overlap is asserted.')


def main():
    import argparse,json
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    args=ap.parse_args();print(json.dumps(verify(json.loads(args.input.read_text())),indent=2))


if __name__=='__main__':main()
