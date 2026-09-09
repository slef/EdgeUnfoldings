"""Exact examples and combinatorial obligations for a two-tree conjecture.

The conjecture is open: for every convex realization with original faces
MINUS_FACES, at least one of the two off-quadrilateral stars via vertex 0
unfolds without positive-area overlap. No routine here proves that claim.
"""
from itertools import product
import json
from pathlib import Path
from n6.certify import require,tree_path
from n6.families import MINUS_FACES as FACES
from n6.polycert import point_spec,make_certificate,make_overlap,verify,verify_overlap
from n6.trees import degree_four_stars,quadrilateral_path_stars

RESULTS=Path(__file__).resolve().parent/'results'
NAMES=['A','B','C','D','P','Q']
FACE_NAMES=['ACBD','ACP','APQ','ADQ','BDQ','BPQ','BCP']
SWAP=(0,1,3,2,5,4)


def paired_trees(anchor=0):
    require(anchor in (0,1),'Anchor must be a degree-four quadrilateral corner')
    return [t for t in degree_four_stars(FACES) if t['apex'] in (4,5) and t['slit_vertex']==anchor]


def select_certificate(spec):
    """Return a replayed certificate or unresolved, never infer success from tolerances."""
    require(spec['faces']==list(map(list,FACES)),'Expected the labelled original minus-edge facets')
    # A supplied certificate may concern a different tree. Its witnesses must
    # not survive into the certificate for the newly selected tree.
    geometry={key:value for key,value in spec.items() if key not in ('pair_witnesses','overlap_witness')}
    reasons=[]
    for tree in paired_trees():
        try:
            cert=make_certificate({**geometry,'cut_edges':tree['cuts']})
            report=verify(cert)
            return {'result':'verified','selected_apex':tree['apex'],'certificate':cert,'verification':report}
        except ValueError as error:reasons.append(str(error))
    return {'result':'unresolved','reasons':reasons,
            'scope':'Neither candidate was certified at the current precision. This does not establish overlap or refute the conjecture.'}


def obligations():
    """The 49 simultaneous pair failures have 28 orbits under exchanging P,Q."""
    first,second=paired_trees()
    face_map={i:next(j for j,g in enumerate(FACES) if {SWAP[v] for v in f}==set(g))
              for i,f in enumerate(FACES)}
    def mapped(pair):return tuple(sorted(face_map[i] for i in pair))
    require(set(map(mapped,first['pairs']))==set(second['pairs']),'Symmetry does not exchange the residual pairs')
    require({tuple(sorted(SWAP[v] for v in e)) for e in first['cuts']}==set(second['cuts']),
            'Symmetry does not exchange the cut trees')
    cells=set(product(first['pairs'],second['pairs']));orbits=[]
    while cells:
        cell=min(cells);orbit={cell,(mapped(cell[1]),mapped(cell[0]))}
        require(orbit<=cells,'Failure cases were counted inconsistently')
        cells-=orbit;orbits.append(sorted(orbit))
    require(len(first['pairs'])==len(second['pairs'])==7,'Unexpected residual pair count')
    return {'result':'verified_combinatorial_reduction','trees':paired_trees(),
            'shared_vertex_pairs_per_tree':14,'residual_pairs_per_tree':7,
            'simultaneous_failure_cases':49,'symmetry_classes':len(orbits),'orbits':orbits,
            'scope':'If all 28 classes are impossible for every convex realization, the two-tree conjecture follows. No class is proved impossible here.'}


def proof_progress():
    """Apply Pinciu's face-neighborhood theorem to the original 28 classes.

    This checks the combinatorial hypotheses of a cited mathematical theorem;
    it is not a formal proof of that theorem or of the two-tree conjecture.
    """
    original=obligations();exclusions=[]
    for tree in paired_trees():
        adj={i:[] for i in range(len(FACES))}
        for a,b in tree['hinges']:adj[a].append(b);adj[b].append(a)
        exclusions.append([dict(faces=pair,base=path[1],path=path)
                           for pair in tree['pairs'] if len(path:=tree_path(adj,*pair))==3])
    excluded=[{tuple(item['faces']) for item in items} for items in exclusions]
    classes=[]
    for number,orbit in enumerate(original['orbits'],1):
        statuses=[a in excluded[0] or b in excluded[1] for a,b in orbit]
        require(len(set(statuses))==1,'Theorem exclusions must respect the symmetry')
        classes.append(dict(id=number,orbit=orbit,
                            status='excluded_by_face_neighborhood' if statuses[0] else 'open'))
    closed=sum(c['status']!='open' for c in classes)
    return dict(schema='n6-minus-pair-proof-progress-v1',result='checked_theorem_application',
                theorem=dict(author='Val Pinciu',year=2007,number=1,
                             title='On the Fewest Nets Problem for Convex Polyhedra',
                             url='https://cccg.ca/proceedings/2007/01a4.pdf'),
                pair_exclusions=exclusions,original_symmetry_classes=len(classes),
                excluded_classes=closed,remaining_classes=len(classes)-closed,
                remaining_failure_combinations=sum(len(c['orbit']) for c in classes if c['status']=='open'),
                remaining_pairs_per_tree=[len(t['pairs'])-len(e) for t,e in zip(paired_trees(),exclusions)],
                classes=classes,
                scope='Universal exclusions for convex realizations with the stated original facets, by the cited theorem. The remaining classes and the two-tree conjecture are open.')


def verify_bundle(bundle):
    require(bundle.get('schema')=='n6-minus-family-examples-v1','Unknown audit schema')
    family=bundle['family']
    require(family in ('quad_paths','off_quad_pair_via_0'),'Unknown candidate family')
    trees=quadrilateral_path_stars(FACES) if family=='quad_paths' else paired_trees()
    remaining={tuple(t['cuts']) for t in trees};coordinates=None;outcomes=[]
    for case in bundle['cases']:
        cert=case['certificate'];cuts=tuple(sorted(map(tuple,cert['cut_edges'])))
        require(cuts in remaining,'Missing, repeated, or extraneous tree')
        remaining.remove(cuts)
        require(cert['faces']==list(map(list,FACES)),'Wrong original facets')
        require(cert['parameter_box']==[],'Expected one exact shape')
        if coordinates is None:coordinates=cert['coordinate_polynomials']
        require(cert['coordinate_polynomials']==coordinates,'Trees refer to different shapes')
        report=verify_overlap(cert) if 'overlap_witness' in cert else verify(cert)
        outcomes.append({'cuts':cert['cut_edges'],'report':report})
    require(not remaining,'The family audit omits trees')
    failures=sum(x['report']['result']=='verified_positive_area_overlap' for x in outcomes)
    return {'result':'verified_family_failure' if failures==len(trees) else 'verified_mixed_example' if failures else 'verified_successful_example',
            'family':family,'verified_failures':failures,'verified_successes':len(trees)-failures,
            'outcomes':outcomes,'scope':'This exact shape and these specified trees only; the universal two-tree conjecture remains open.'}


def make_bundle(points,trees,family):
    cases=[]
    for tree in trees:
        spec=point_spec(points,FACES,tree['cuts'])
        try:cert=make_certificate(spec)
        except ValueError:
            cert=None
            for a,b in tree['pairs']:
                try:cert=make_overlap(spec,a,b);break
                except ValueError:pass
            if cert is None:raise ValueError('No exact outcome found for this tree')
        cases.append({'apex':tree['apex'],'slit_vertex':tree['slit_vertex'],'certificate':cert})
    bundle={'schema':'n6-minus-family-examples-v1','family':family,'cases':cases}
    verify_bundle(bundle);return bundle


def write(name,data):
    (RESULTS/name).write_text(json.dumps(data,indent=2)+'\n')


def generate():
    quad=[[0,0,0],[10,0,0],[18,-5,0],[-27,10,0],[22,-5,-1],[-62,24,-5]]
    switching=[[0,0,0],[10,0,0],[16,-3,0],[-42,13,0],[-58,0,-6],[-133,9,-10]]
    reflected=[[switching[SWAP[v]][0],-switching[SWAP[v]][1],switching[SWAP[v]][2]] for v in range(6)]
    for name,p,trees,family in (
        ('minus-quad-paths',quad,quadrilateral_path_stars(FACES),'quad_paths'),
        ('minus-pair-switch',switching,paired_trees(),'off_quad_pair_via_0'),
        ('minus-pair-switch-reflected',reflected,paired_trees(),'off_quad_pair_via_0')):
        bundle=make_bundle(p,trees,family);report=verify_bundle(bundle)
        write(name+'.certificate.json',bundle);write(name+'.verification.json',report)
    # Standalone forms keep the displayed model and net tied to exact evidence.
    bundle=make_bundle(switching,paired_trees(),'off_quad_pair_via_0')
    for case in bundle['cases']:
        write('minus-pair-'+('P' if case['apex']==4 else 'Q')+'.certificate.json',case['certificate'])
    write('minus-pair-obligations.json',obligations())


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=('generate','verify','obligations','progress','unfold','cover'))
    ap.add_argument('input',type=Path,nargs='?');ap.add_argument('--bits',type=int,default=80)
    args=ap.parse_args()
    if args.action in ('verify','unfold') and args.input is None:ap.error('An input file is required')
    from n6.intervals import set_precision
    set_precision(args.bits)
    if args.action=='generate':generate();print('Generated and independently replayed three exact examples.')
    elif args.action=='obligations':print(json.dumps(obligations(),indent=2))
    elif args.action=='progress':print(json.dumps(proof_progress(),indent=2))
    elif args.action=='unfold':print(json.dumps(select_certificate(json.loads(args.input.read_text())),indent=2))
    elif args.action=='cover':
        from n6.cover import read_cover,generate as generate_cover,verify as verify_cover,summary
        base=read_cover(RESULTS/'minus-merged-cover.certificate.json.gz')['geometry']
        path=RESULTS/'minus-pair-cover.partial.json.gz'
        candidate=generate_cover(base,path,max_seconds=120,candidates=2,candidate_trees=paired_trees())
        if summary(candidate).get('unresolved',0):print(json.dumps(summary(candidate),indent=2))
        else:
            report=verify_cover(candidate)
            path.replace(RESULTS/'minus-pair-cover.certificate.json.gz')
            write('minus-pair-cover.verification.json',report);print(json.dumps(report,indent=2))
    else:print(json.dumps(verify_bundle(json.loads(args.input.read_text())),indent=2))
