"""Fixed exact certificates for the seven trees in PRISM_EDGE_PROOF.md.

The universal claim is a written geometric proof. This implementation
independently certifies a single tree on the supplied exact domain; failure
to resolve one uniform tree on a parameter box is not a counterexample.
"""
from n6.certify import require
from n6.families import PRISM_FACES,PRISM_CUTS
from n6.flat_octahedron import original_candidates,curvature_bands
from n6.polycert import Geometry,make_certificate,verify as all_pairs
from n6.prism_angle_identities import verify as identities


def candidates():
    _,near=original_candidates(PRISM_FACES)
    return [dict(name='source_%s_slit_%s'%(t['source'],t['slit']),cut_edges=[list(e) for e in t['cuts']]) for t in near]+[dict(name='triangular_chain_fallback',cut_edges=[list(e) for e in PRISM_CUTS])]


def select(spec):
    g=Geometry(spec)
    require({frozenset(f) for f in g.faces}=={frozenset(f) for f in PRISM_FACES},'Expected the stated original prism facets and labels')
    bands=curvature_bands(g)
    if all(b in ('<','=') for b in bands.values()):regime='all_curvatures_at_most_pi'
    elif any(bands[v] in ('>','=') for v in (2,5)):regime='sharp_fan_switch'
    elif any(bands[v] in ('>','=') for v in (0,4)):regime='outer_vertex_gate_switch'
    elif any(bands[v] in ('>','=') for v in (1,3)):regime='sharp_original_source_direct_or_forced_gate'
    else:regime='curvature_branch_not_uniformly_resolved'
    clean={k:v for k,v in spec.items() if k not in ('pair_witnesses','overlap_witness','original_rule_selection','path_selection')}
    attempts=[]
    for t in candidates():
        try:
            cert=make_certificate({**clean,'cut_edges':t['cut_edges']});replay=all_pairs(cert)
        except ValueError as e:
            attempts.append(dict(candidate=t['name'],result='not_certified',reason=str(e)));continue
        return dict(result='verified_prism_seven_candidate_choice',candidate=t['name'],
                    cut_edges=t['cut_edges'],curvature_comparisons_with_pi=bands,
                    theorem_regime=regime,earlier_candidates=attempts,independent_all_original_pairs=replay,
                    certificate=cert,written_existence_proof='PRISM_EDGE_PROOF.md',
                    exact_angle_identity_audit=identities(),
                    scope='One original tree is certified throughout this explicit domain. The universal seven-candidate theorem is a separate written proof, pending independent review.')
    raise ValueError('No single candidate certified uniformly on this domain; subdivide or improve exact comparisons. This does not refute the pointwise written theorem.')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--certificate',type=Path);args=ap.parse_args()
    spec=json.loads(args.input.read_text());set_precision(spec.get('suggested_fractional_bits',240))
    r=select(spec);cert=r.pop('certificate')
    if args.certificate:args.certificate.write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps(r,indent=2))
