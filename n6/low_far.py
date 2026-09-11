"""Three local checks plus LOW_CURVATURE_FAR_REDUCTION.md; no H or R.

This checks explicit domains and invokes a written conditional theorem.
It is not formal verification of the geometric proof or every-slit Lemma F.
"""
from n6.certify import require
from n6.curvature import angle_product
from n6.regimes import octahedron_frame,curvature_pi
from n6.polycert import PairUnresolved


def setup(spec):
    g,v,w,ring,k,V,W=octahedron_frame(spec)
    bands={x:curvature_pi(angle_product(g.p,g.faces,g.h,x)) for x in range(6)}
    require(all(b in ('<','=') for b in bands.values()),'All-low curvature condition is not certified')
    targets={tuple(sorted(pair)) for pair in [(V[k],V[(k-1)%4]),
             (V[k],W[(k-1)%4]),(V[(k-1)%4],W[k])]}
    return g,targets,bands


def make_certificate(spec):
    g,targets,_=setup(spec);witnesses=[]
    for a,b in sorted(targets):
        found=None
        for owner in (a,b):
            f=g.faces[owner]
            for e in zip(f,f[1:]+f[:1]):
                if all(q.hi<=0 for q in g.separating_bounds(a,b,owner,e)):
                    found=dict(faces=[a,b],owner=owner,edge=list(e));break
            if found:break
        if found is None:raise PairUnresolved(a,b)
        witnesses.append(found)
    return {**{k:v for k,v in spec.items() if k not in ('pair_witnesses','overlap_witness')},
            'local_pair_witnesses':witnesses}


def verify(spec):
    g,remaining,bands=setup(spec);reports=[]
    for witness in spec['local_pair_witnesses']:
        pair=tuple(witness['faces'])
        require(pair in remaining,'Repeated or wrong local target')
        remaining.remove(pair)
        bounds=g.separating_bounds(*pair,witness['owner'],witness['edge'])
        require(all(q.hi<=0 for q in bounds),'Local separator not certified')
        reports.append({**witness,'determinant_bounds':[q.pair() for q in bounds]})
    require(not remaining,'Missing local pair')
    return dict(result='verified_low_curvature_three_local_pair_certificate',
                parameter_dimension=len(g.box),curvature_comparisons_with_pi=bands,
                local_pairs_explicitly_checked=3,far_pairs_implied_by_written_theorem=6,
                H_required=False,R_required=False,whole_net_nonoverlapping=True,
                every_slit_lemma_F_proved=False,local_separators=reports,
                proof='LOW_CURVATURE_FAR_REDUCTION.md',
                scope='The explicit domain has all curvatures <=pi and three safe local pairs in this net. The written conditional proof supplies all six far pairs. This does not assert the local premise at every slit or formally verify the whole geometric proof.')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path)
    args=ap.parse_args();spec=json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(verify(spec),indent=2))
