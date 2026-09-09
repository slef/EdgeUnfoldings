"""Exact witness that one Case-B petal apex enters the outer wedge.

The proposed individual-apex exclusion is stronger than nonoverlap. The saved
example violates that exclusion while all 28 face pairs remain nonoverlapping.
"""
from n6.certify import require,tree_path
from n6.polycert import Geometry
from n6.regimes import classify,positive_angles_pi
from n6.curvature import face_angle
from n6.intervals import det,sub


def verify(cert):
    classification=classify(cert)  # Includes hull, original edges, and H/R.
    claim=cert['apex_entry'];sel=cert['selection'];i=claim['triple_index']
    require(type(i) is int and i in (sel['slit_index'],(sel['slit_index']+1)%4),'Triple crosses the slit')
    require(claim['side']=='left','Only the stated left-apex witness is supported')
    entry=next(t for t in classification['triples'] if t['i']==i)
    require(entry['sum_W_comparison']=='<' and entry['case_A_comparison']=='>','Not the small-fan-angle Case B')
    g=Geometry(cert);v,w=sel['apex'],sel['antipode'];u=sel['equator'];j,jj=(i+1)%4,(i+2)%4
    lookup={frozenset(f):n for n,f in enumerate(g.faces)}
    V=[lookup[frozenset((v,u[t],u[(t+1)%4]))] for t in range(4)]
    W=[lookup[frozenset((w,u[t],u[(t+1)%4]))] for t in range(4)]
    def angle(f,x):return face_angle(g.p,g.faces[f],g.h[f],x)
    total=[angle(W[i],u[j]),angle(W[j],u[j]),angle(W[j],u[jj]),angle(W[jj],u[jj]),angle(V[i],u[j])]
    require(positive_angles_pi(total)=='<','Sigma_W+a < pi is not certified')
    root=W[j]
    def develop(f):return g.develop(tree_path(g.adj,root,f))
    left,right,fan=develop(V[i]),develop(V[jj]),develop(root)
    def side_pair(X,a,b,p):
        d=sub(X[b],X[a])
        return det(d,sub(fan[w],X[a])),det(d,sub(p,X[a]))
    def opposite(a,b):return a.lo>0 and b.hi<0 or a.hi<0 and b.lo>0
    own=side_pair(left,u[j],u[i],left[v])
    other=side_pair(right,u[jj],u[(jj+1)%4],left[v])
    require(opposite(*own) and opposite(*other),'Apex is not certified inside both outer half-planes')
    far=side_pair(right,u[jj],u[(jj+1)%4],left[u[i]])
    require(opposite(*far),'Far equator vertex is not certified past X')
    # The entire right triangle stays outside the left outer half-plane.
    right_sides=[side_pair(left,u[j],u[i],right[t]) for t in g.faces[V[jj]]]
    require(all(a.lo>0 and b.lo>0 or a.hi<0 and b.hi<0 for a,b in right_sides),
            'The opposite petal escape from the wedge is not certified')
    return dict(result='verified_failure_of_individual_apex_exclusion',
                apex=v,antipode=w,slit_vertex=u[sel['slit_index']],equator=u,triple_index=i,
                angle_comparison='Sigma_W+a < pi',left_apex_strictly_inside_outer_wedge=True,
                right_petal_strictly_outside_outer_wedge=True,left_far_vertex_strictly_past_X=True,
                far_vertex_determinants=[x.pair() for x in far],
                outer_halfplane_determinants=[[x.pair() for x in pair] for pair in (own,other)],
                right_petal_separation_determinants=[[x.pair() for x in pair] for pair in right_sides],
                scope='Refutes the stronger assertion that each individual apex stays outside the outer wedge. Does not refute opposite-petal nonoverlap or edge unfolding.',
                curvature_order=classification['curvature_order'])


def main():
    import argparse,json
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    args=ap.parse_args();print(json.dumps(verify(json.loads(args.input.read_text())),indent=2))


if __name__=='__main__':main()
