"""Check the hypotheses of the complete selected octahedron net theorem.

The universal geometric proof is LEMMA_F_CHORD.md together with its listed
dependencies. This program checks explicit coordinate domains, not the
correctness of every geometric step of that written proof.
"""
import json
from pathlib import Path

from n6.curvature import angle_product
from n6.polycert import Geometry
from n6.regimes import classify, curvature_pi


def verify(spec):
    classification = classify(spec)
    g = Geometry(spec)
    s = spec['selection']
    v,w,ring,k = (s[n] for n in ('apex','antipode','equator','slit_index'))
    band = curvature_pi(angle_product(g.p,g.faces,g.h,v))
    proof_branch = ('high_curvature_pole_angle' if band=='>' else
                    'low_curvature_equal_lengths' if band=='<' else
                    'equality_covered_by_both_proofs' if band=='=' else
                    'curvature_unresolved_but_both_branches_proved')
    c = ring[k]
    faces = [[w,c,ring[(k+1)%4]], [w,c,ring[(k+3)%4]]]
    return dict(result='verified_selected_octahedron_hypotheses',
                parameter_dimension=len(g.box), selected_source=v, fan_vertex=w,
                selected_slit=c, curvature_order=classification['curvature_order'],
                source_curvature_comparison_with_pi=band, proof_branch=proof_branch,
                low_curvature_face_complements=[dict(face=f,complement=sorted(set(range(6))-set(f))) for f in faces],
                all_28_pairs_proved_by_written_theorem=True,
                whole_selected_net_nonoverlapping=True,
                every_slit_lemma_F_proved=False, full_n6_proved=False,
                theorem_dependencies=['LEMMA_F_CHORD.md','LEMMA_F_POLE_ANGLE.md',
                                      'LEMMA_L_PROOF.md','LEMMA_F_CUT_RAYS.md',
                                      'LEMMA_F_CUT_REDUCTION.md','CASE_PARTITION.md',
                                      'HINGE_AUDIT.md'],
                scope='Every parameter tuple in the explicit domain satisfies the hypotheses of the written universal selected-net theorem. The geometric proof is a dependency, not formally verified by this program. The every-slit Lemma F and nonsimplicial n=6 cases are separate.')


def main():
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',type=Path)
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(verify(spec),indent=2))


if __name__ == '__main__':
    main()
