"""Two exact slit-side pair certificates plus the geometric Lemma F reduction.

This proves whole-net safety only on the supplied point or parameter region.
The universal reduction is LEMMA_F_CUT_REDUCTION.md; the two retained pair
claims remain open for arbitrary convex octahedra satisfying H and R.
"""
import json
from pathlib import Path

from n6.certify import require, tree_path
from n6.intervals import det, sub
from n6.polycert import Geometry, PairUnresolved
from n6.regimes import classify


def labels(spec, g):
    s = spec['selection']
    v, w, ring, k = (s[x] for x in ('apex', 'antipode', 'equator', 'slit_index'))
    lookup = {frozenset(f): t for t, f in enumerate(g.faces)}
    V = [lookup[frozenset((v, ring[t], ring[(t+1)%4]))] for t in range(4)]
    W = [lookup[frozenset((w, ring[t], ring[(t+1)%4]))] for t in range(4)]
    return v, w, ring, k, V, W


def targets(spec, g):
    _, _, _, k, V, W = labels(spec, g)
    return [(V[(k+2)%4], W[k]), (V[(k+1)%4], W[(k+3)%4])]


def make_certificate(spec):
    classify(spec)  # Independently check the hull, the exact cuts, H, and R.
    g = Geometry(spec)
    witnesses = []
    for pair in targets(spec, g):
        a, b = sorted(pair)
        found = None
        for owner in (a, b):
            f = g.faces[owner]
            for e in zip(f, f[1:]+f[:1]):
                if all(q.hi <= 0 for q in g.separating_bounds(a, b, owner, e)):
                    found = dict(faces=[a,b], owner=owner, edge=list(e))
                    break
            if found:
                break
        if found is None:
            raise PairUnresolved(a, b)
        witnesses.append(found)
    clean = {key: value for key, value in spec.items() if key not in
             ('pair_witnesses', 'overlap_witness', 'angular_claims', 'apex_entry')}
    return {**clean, 'far_pair_witnesses': witnesses}


def small_fan_cases(spec, g, classification):
    """Illustrate the exact slit-far/near-X corollary, without needing it."""
    _, w, ring, k, V, W = labels(spec, g)
    cases = []
    for t in classification['triples']:
        i = t['i']; j = (i+1)%4; h = (i+2)%4
        entry = dict(triple_index=i, fan_angle_sum=t['sum_W_comparison'])
        if t['sum_W_comparison'] == '<':
            root = W[j]
            def develop(f):
                return g.develop(tree_path(g.adj, root, f))
            fan = develop(root)
            # The retained petal is the one NOT attached to the slit-side fan.
            other = h if i == k else i
            end = i if i == k else h
            petal, target = develop(V[other]), develop(W[end])
            a, b = ring[other], ring[(other+1)%4]
            d = sub(petal[b], petal[a])
            reference = det(d, sub(fan[w], petal[a]))
            slit_side = det(d, sub(target[ring[k]], petal[a]))
            near = (reference.lo > 0 and slit_side.lo >= 0 or
                    reference.hi < 0 and slit_side.hi <= 0)
            past = (reference.lo > 0 and slit_side.hi < 0 or
                    reference.hi < 0 and slit_side.lo > 0)
            entry.update(slit_far_vertex=('at_or_before_X' if near else
                                          'strictly_past_X' if past else 'unresolved'),
                         base_halfplane_proves_both_pairs=near,
                         halfplane_determinants=[reference.pair(), slit_side.pair()])
        cases.append(entry)
    return cases


def verify(spec):
    classification = classify(spec)
    g = Geometry(spec)
    remaining = {tuple(sorted(pair)) for pair in targets(spec, g)}
    reports = []
    for witness in spec['far_pair_witnesses']:
        pair = tuple(witness['faces'])
        require(pair in remaining, 'Repeated, missing, or wrong slit-side target pair')
        remaining.remove(pair)
        bounds = g.separating_bounds(*pair, witness['owner'], witness['edge'])
        require(all(q.hi <= 0 for q in bounds), 'Unverified slit-side pair separator')
        reports.append(dict(faces=list(pair), owner=witness['owner'], edge=witness['edge'],
                            determinant_bounds=[q.pair() for q in bounds]))
    require(not remaining, 'Missing slit-side target pair')
    return dict(result='verified_two_pair_net_certificate',
                parameter_dimension=len(g.box), curvature_order=classification['curvature_order'],
                explicitly_checked_far_pairs=2, conditionally_implied_far_pairs=4,
                whole_selected_net_nonoverlapping=True,
                universal_lemma_F_proved=False,
                pair_separators=reports, small_fan_cases=small_fan_cases(spec, g, classification),
                theorem_dependencies=['shared-vertex wedge lemma', 'LEMMA_L_PROOF.md',
                                      'Case A and base-cone proofs in CASE_PARTITION.md',
                                      'LEMMA_F_CUT_REDUCTION.md',
                                      'interior-fan reduction in HINGE_AUDIT.md'],
                scope='The two exact separators and geometric reduction certify this explicit region only. The two universal slit-side pair claims remain open.')


def main():
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 240))
    print(json.dumps(verify(spec), indent=2))


if __name__ == '__main__':
    main()
