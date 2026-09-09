"""Exact checks of the hypotheses of the convex-patch unfolding lemmas.

The universal proofs are written in OCTA_CONVEX_PATCHES.md. This checker
certifies hypotheses on a specified point or region; it is not a formal
verification of those mathematical proofs. Numerical surveys are separate.
"""
import json
from pathlib import Path
from n6.certify import require
from n6.polycert import Geometry, point_spec, make_certificate, verify
from n6.curvature import face_angle, verify_order
from n6.regimes import positive_angles_pi


def geometry_patches(g, selection):
    """Check the octahedral labels and classify four flattened patches."""
    v, w, ring = selection['apex'], selection['antipode'], selection['equator']
    require(v != w and len(ring) == len(set(ring)) == 4 and set(ring)|{v,w} == set(range(6)), 'Invalid poles or equator')
    required = {frozenset((pole, ring[i], ring[(i+1)%4])) for pole in (v,w) for i in range(4)}
    lookup = {frozenset(f): i for i,f in enumerate(g.faces)}
    require(set(lookup) == required, 'Expected exactly the eight octahedral triangles')
    patches = []
    for i in range(4):
        a,b = ring[i],ring[(i+1)%4]
        faces = [lookup[frozenset((pole,a,b))] for pole in (w,v)]
        relations = [positive_angles_pi([face_angle(g.p, g.faces[f], g.h[f], u) for f in faces]) for u in (a,b)]
        require(None not in relations, 'Patch corner relation remains unresolved')
        require(relations != ['>','>'], 'A simple two-triangle patch cannot have two reflex corners')
        patches.append(dict(index=i, equator_edge=[a,b], corner_relations_to_pi=relations,
                            convex=all(r in ('<','=') for r in relations)))
    return patches


def classify(spec):
    g = Geometry(spec)
    selection = spec['selection']
    v, w, ring = selection['apex'], selection['antipode'], selection['equator']
    patches = geometry_patches(g, selection)
    nonconvex = [p['index'] for p in patches if not p['convex']]
    require(len(nonconvex) <= 3, 'Contradicts the convex-patch existence lemma')
    # The all-convex theorem does not need H. In particular, do not reject a
    # symmetric all-convex shape because interval comparison cannot resolve
    # equal curvatures. The other reports explicitly retain H.
    ranking = verify_order(g, [(v,x) for x in range(6) if x != v]) if nonconvex else None
    if not nonconvex:
        regime = 'zero'; choices = list(range(4)); theorem = 'Every slit succeeds by disjoint angular wedges'
    elif len(nonconvex) == 1:
        regime = 'one'; j = nonconvex[0]; choices = [(j+2)%4,(j+3)%4]
        theorem = 'The two stated fixed-source slits make local pairs safe, and one makes both opposite-petal pairs safe under H. Fixed sharpest-source whole-net success remains open. OCTA_ONE_PATCH.md proves existence using two prescribed trees with different four-cut poles.'
    else:
        regime = 'three' if len(nonconvex) == 3 else 'two-adjacent' if (nonconvex[1]-nonconvex[0])%4 in (1,3) else 'two-opposite'
        choices = []
        directions = {'B' if patches[i]['corner_relations_to_pi'][0] == '>' else 'F' for i in nonconvex}
        theorem = ('OCTA_PATCH_BUDGET.md proves existence using prescribed trees with either four-cut pole.'
                   if len(nonconvex) == 2 or len(directions) == 2 else
                   'The common-direction three-patch family remains open in general.')
    return dict(result='verified_patch_hypotheses', regime=regime, patches=patches,
                nonconvex_patches=nonconvex, curvature_order=ranking, sharpest_apex_required=bool(nonconvex),
                candidate_slit_indices=choices, candidate_slit_vertices=[ring[k] for k in choices],
                conclusion=theorem,
                scope='These exact coordinates or this parameter region satisfy the checked hypotheses. The stated general conclusion invokes the written geometric lemmas; an individual net requires its own all-pairs certificate.')


def survey(samples, seed):
    import numpy as np
    from durer_small_n.octa import Octa, rand_points, octa_structure
    from n6.original_star_probe import apex_curvature
    rng = np.random.default_rng(seed)
    counts = {}; first = {}; n = 0
    while n < samples:
        p = rand_points(6,rng); st = octa_structure(p)
        if st is None:
            continue
        faces,adj = st
        v = max(range(6), key=lambda x:apex_curvature(p,faces,x))
        o = Octa(p,v,faces,adj)
        bad = [i for i in range(4) if max(o.e[i],o.f[i]) > np.pi+1e-10]
        key = ['zero','one','two','three','four'][len(bad)]
        if len(bad) == 2:
            key += '-adjacent' if (bad[1]-bad[0])%4 in (1,3) else '-opposite'
        counts[key] = counts.get(key,0)+1
        if key not in first:
            first[key] = dict(points=p.tolist(), apex=v, antipode=o.w, equator=o.u, nonconvex=bad)
        n += 1
    return dict(scope='Numerical classification only, neither an exact certificate nor a fraction of all octahedra covered.',
                samples=n, seed=seed, counts=counts, first=first)


def examples(report, output_dir):
    import numpy as np
    from n6.octa_patterns import FACES
    from n6.intervals import set_precision
    set_precision(192)
    results = []
    for name, source in sorted(report['first'].items()):
        raw = np.array(source['points'])[[source['apex'],source['antipode']]+source['equator']]
        raw = (raw-raw[0])/np.max(np.linalg.norm(raw[:,None]-raw[None],axis=-1))
        selected = None
        for scale in (100,1000,10000,100000,1000000):
            p = np.rint(raw*scale).astype(int).tolist()
            spec = point_spec(p,FACES,[(0,u) for u in range(2,6)]+[(1,2)])
            spec['selection'] = dict(apex=0,antipode=1,equator=[2,3,4,5])
            try:
                classification = classify(spec)
            except ValueError:
                continue
            if classification['regime'] != name:
                continue
            choices = classification['candidate_slit_vertices'] or list(range(2,6))
            for u in choices:
                spec['cut_edges'] = [[0,x] for x in range(2,6)]+[[1,u]]
                try:
                    cert = make_certificate(spec)
                    verification = verify(cert)
                except ValueError:
                    continue
                selected = cert,dict(classification=classification, net=verification,
                                     fractional_bits=192, scope='One exact example. The open regimes are not settled by their successful examples.')
                break
            if selected:
                break
        if selected is None:
            raise ValueError('Could not exactly certify example '+name)
        stem = 'octa-patches-'+name
        selected[0]['suggested_fractional_bits'] = 192
        (output_dir/(stem+'.certificate.json')).write_text(json.dumps(selected[0],indent=2)+'\n')
        (output_dir/(stem+'.verification.json')).write_text(json.dumps(selected[1],indent=2)+'\n')
        results.append(dict(regime=name, points=p, nonconvex_patches=classification['nonconvex_patches'],
                            successful_slit_vertex=u, certificate=stem+'.certificate.json'))
    return results


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--verify', type=Path)
    ap.add_argument('--samples', type=int, default=5000)
    ap.add_argument('--seed', type=int, default=6090942)
    ap.add_argument('--output', type=Path, default=Path('n6/results/octa-patch-survey.json'))
    ap.add_argument('--examples', action='store_true')
    args = ap.parse_args()
    if args.verify:
        from n6.intervals import set_precision
        spec = json.loads(args.verify.read_text()); set_precision(spec.get('suggested_fractional_bits',192))
        print(json.dumps(classify(spec),indent=2))
    else:
        require(args.samples > 0, 'Sample count must be positive')
        report = survey(args.samples,args.seed)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
        if args.examples:
            result = examples(report,args.output.parent)
            (args.output.parent/'octa-patch-examples.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:v for k,v in report.items() if k!='first'},indent=2))
