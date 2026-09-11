"""Exact fixed-tree selections using the written full minus-edge theorem.

An unresolved interval choice is rejected. The universal theorem is the
geometric proof in MINUS_EDGE_PROOF.md, not a claim that this finite-precision
selector terminates on every input box.
"""
from n6.certify import require
from n6.families import MINUS_FACES
from n6.polycert import Geometry
from n6.flat_octahedron import original_candidates, curvature_bands, verify_fixed_tree
from n6.minus_complementary_sources import select as complementary
from n6.prism_paths import polygon_angle_product
from n6.slit_threshold import weighted_slit_pi


def select(spec):
    g=Geometry(spec)
    require({frozenset(f) for f in g.faces}=={frozenset(f) for f in MINUS_FACES},
            'Expected the stated original minus-edge labels')
    bands=curvature_bands(g); _,trees=original_candidates(g.faces)
    for t in trees:
        if not (all(b in ('<','=') for b in bands.values()) or bands[t['source']] in ('>','=')):continue
        try:chosen=verify_fixed_tree({**spec,'cut_edges':t['cuts']})
        except ValueError:continue
        return dict(result='verified_minus_edge_theorem_fixed_choice',branch='direct_source_threshold',
                    cut_edges=[list(e) for e in t['cuts']],fixed_tree_proof=chosen,
                    proof='MINUS_EDGE_PROOF.md',whole_original_net_safe=True,
                    scope='Exact hypotheses for this fixed tree; the universal written proof awaits independent review.')
    chosen=complementary(spec)
    failures={}
    totals={x:polygon_angle_product(g,x) for x in range(6)}
    for v,w,ends in [(4,3,(0,1,5)),(5,2,(0,1,4))]:
        if bands[v] not in ('>','='):continue
        values={c:weighted_slit_pi(totals[c],totals[w]) for c in ends}
        if all(x=='<' for x in values.values()):failures[v]=values
    return dict(result='verified_minus_edge_theorem_fixed_choice',
                branch='failed_sharp_source_forces_complementary_gates' if failures else 'complementary_corner',
                failed_direct_thresholds=failures,cut_edges=chosen['cut_edges'],
                fixed_tree_proof=chosen,proof='MINUS_EDGE_PROOF.md',whole_original_net_safe=True,
                scope='Exact hypotheses for this fixed tree; the universal written proof awaits independent review.')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    args=ap.parse_args();spec=json.loads(args.input.read_text())
    set_precision(spec.get('suggested_fractional_bits',240));print(json.dumps(select(spec),indent=2))
