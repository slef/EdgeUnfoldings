"""Exact local failure under H, with every curvature below pi and all far pairs safe.

This refutes the stronger all-slits whole-net claim, not every-slit Lemma F.
The R-selected tree of the same solid has a separate all-28 certificate.
"""
import itertools
import json
from pathlib import Path
from n6.certify import require,tree_path
from n6.intervals import set_precision
from n6.low_far import setup
from n6.polycert import (Geometry,point_spec,make_overlap,verify_overlap,
                        make_certificate as all_certificate,verify as all_pairs)
from n6.curvature import angle_product,interval_angle_le,verify_order


def specification():
    points=[[0,0,0],[-3687,-92873,-36891],[-2018,-50170,-13335],
            [-1507,-28468,-1874],[-3551,-89787,-43776],[570,2929,-11034]]
    faces=[[1,2+i,2+(i+1)%4] for i in range(4)]+[[0,2+(i+1)%4,2+i] for i in range(4)]
    return {**point_spec(points,faces,[[0,5],[1,5],[2,5],[4,5],[2,3]]),
            'selection':dict(apex=5,antipode=3,equator=[0,4,1,2],slit_index=3),
            'suggested_fractional_bits':240}


def make_certificate():
    spec=specification();g=Geometry(spec);bad={(3,4),(3,7)};safe=[]
    for a,b in itertools.combinations(range(8),2):
        if (a,b) in bad:continue
        path=tree_path(g.adj,a,b);common=set.intersection(*(set(g.faces[f]) for f in path))
        if common:
            safe.append(dict(faces=[a,b],kind='vertex_fan',vertex=min(common)));continue
        found=None
        for owner in (a,b):
            f=g.faces[owner]
            for e in zip(f,f[1:]+f[:1]):
                if all(q.hi<=0 for q in g.separating_bounds(a,b,owner,e)):
                    found=dict(faces=[a,b],kind='separating_edge',owner=owner,edge=list(e));break
            if found:break
        require(found is not None,'Safe pair not certified');safe.append(found)
    return {**spec,'overlap_witnesses':[make_overlap(spec,*pair)['overlap_witness'] for pair in sorted(bad)],
            'nonoverlap_witnesses':safe}


def verify(cert):
    g,local,bands=setup(cert);s=cert['selection'];v=s['apex'];c=s['equator'][s['slit_index']]
    require(all(b=='<' for b in bands.values()),'This example must be strictly below pi')
    source_order=verify_order(g,[(v,x) for x in range(6) if x!=v])
    z={x:angle_product(g.p,g.faces,g.h,x) for x in s['equator']}
    sharper=[x for x in s['equator'] if x!=c and interval_angle_le(z[c],z[x]) is False]
    require(bool(sharper),'A strict failure of R must be certified')
    remaining=set(itertools.combinations(range(8),2));overlap=[];methods={}
    for witness in cert['overlap_witnesses']:
        pair=tuple(witness['faces'])
        require(pair in remaining and pair in local,'Repeated or nonlocal overlap target')
        remaining.remove(pair);overlap.append(verify_overlap({**cert,'overlap_witness':witness}))
    require(len(overlap)==2,'Expected exactly two local overlaps')
    for witness in cert['nonoverlap_witnesses']:
        pair=tuple(witness['faces']);require(pair in remaining,'Repeated or wrong safe pair')
        remaining.remove(pair);a,b=pair;kind=witness['kind']
        if kind=='vertex_fan':
            require(all(witness['vertex'] in g.faces[f] for f in tree_path(g.adj,a,b)),
                    'Not the same uncut vertex copy')
        elif kind=='separating_edge':
            require(all(q.hi<=0 for q in g.separating_bounds(a,b,witness['owner'],witness['edge'])),
                    'Safe separator not certified')
        else:raise ValueError('Unknown safe-pair method')
        methods[kind]=methods.get(kind,0)+1
    require(not remaining,'Missing face pairs')
    return dict(result='verified_local_failure_under_H_and_strictly_low_curvature',
                curvature_comparisons_with_pi=bands,H=source_order,R_fails=True,
                vertices_strictly_sharper_than_slit=sharper,overlap=overlap,
                nonoverlapping_pairs=26,safe_pair_methods=methods,all_six_far_pairs_safe=True,
                refutes_every_slit_lemma_F=False,
                scope='Exactly two local pairs overlap and every other pair is safe in this net. The source is sharpest and every curvature is below pi, but R fails. This refutes all-slits whole-net safety, not the far-only Lemma F or octahedral unfoldability.')


def repair():
    spec=specification();g=Geometry(spec);s=spec['selection'];ring=s['equator']
    for k,c in enumerate(ring):
        try:verify_order(g,[(c,x) for x in ring if x!=c])
        except ValueError:continue
        spec['selection']={**s,'slit_index':k}
        spec['cut_edges']=[[s['apex'],u] for u in ring]+[[s['antipode'],c]]
        return all_certificate(spec)
    raise ValueError('Maximum-curvature slit unresolved')


def main():
    set_precision(240);root=Path(__file__).parent/'results';cert=make_certificate();fixed=repair()
    for name,c,r in [('low-local-failure',cert,verify(cert)),('low-local-repair',fixed,all_pairs(fixed))]:
        for suffix,data in [('certificate',c),('verification',r)]:
            (root/f'{name}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(name,r['result'],flush=True)


if __name__=='__main__':main()
