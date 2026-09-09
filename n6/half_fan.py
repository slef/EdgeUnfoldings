"""Exact hypotheses and cut selection for the half-fan patch theorems.

The geometric proofs are in OCTA_HALF_FAN.md. A successful hypothesis check
invokes those proofs; the independent polycert checker can verify the net.
"""
import json
from pathlib import Path
from n6.certify import require, edge
from n6.polycert import Geometry
from n6.convex_patches import geometry_patches
from n6.curvature import face_angle, angle_product, verify_order
from n6.regimes import curvature_pi, positive_angles_pi


def opening(directions):
    """Select the table's slit, with directions '', 'F', or 'B'."""
    require(len(directions) == 4 and set(directions) <= {'', 'F', 'B'},
            'Invalid patch directions')
    bad = [i for i, d in enumerate(directions) if d]
    if len(bad) == 1:
        i, = bad
        return (i + (2 if directions[i] == 'F' else 3)) % 4
    require(len(bad) == 2, 'The theorem requires one or two bad patches')
    require((bad[1]-bad[0]) % 4 in (1, 3), 'The two bad patches must be adjacent')
    i = next(j for j in bad if (j+1) % 4 in bad)
    pair = directions[i] + directions[(i+1) % 4]
    require(pair != 'FB', 'Two patches cannot be reflex at their common vertex')
    return (i + {'FF': 2, 'BB': 0, 'BF': 3}[pair]) % 4


def setup(g, source, fan, ring):
    patches = geometry_patches(g, dict(apex=source, antipode=fan, equator=ring))
    lookup = {frozenset(f): i for i, f in enumerate(g.faces)}
    for i in range(4):
        f = g.faces[lookup[frozenset((fan, ring[i], ring[(i+1) % 4]))]]
        j = f.index(fan)
        require(f[(j+1) % 3] == ring[i] and f[(j+2) % 3] == ring[(i+1) % 4],
                'Equator orientation disagrees with fan facets')
    directions = ['B' if p['corner_relations_to_pi'][0] == '>' else
                  'F' if p['corner_relations_to_pi'][1] == '>' else '' for p in patches]
    return patches, directions, lookup


def two_angle_indices(directions):
    bad = [i for i, d in enumerate(directions) if d]
    require(len(bad) == 1, 'The two-angle test requires exactly one bad patch')
    i, = bad
    return [(i+2) % 4, (i + (3 if directions[i] == 'F' else 1)) % 4]


def two_angle_relation(g, lookup, pole, ring, indices):
    angles = []
    for i in indices:
        f = lookup[frozenset((pole, ring[i], ring[(i+1) % 4]))]
        angles.append(face_angle(g.p, g.faces[f], g.h[f], pole))
    return positive_angles_pi(angles)


def hypotheses(spec):
    g = Geometry(spec)
    claim = spec['half_fan']
    v, w, ring = claim['source'], claim['fan_vertex'], claim['equator']
    patches, directions, lookup = setup(g, v, w, ring)
    k = opening(directions)
    criterion = claim['criterion']
    detail = {}
    if criterion == 'curvature':
        relation = curvature_pi(angle_product(g.p, g.faces, g.h, w))
        require(relation in ('>', '='), 'Cannot certify fan curvature at least pi')
        detail['fan_curvature_relation_to_pi'] = relation
    else:
        require(criterion == 'two_angles', 'Unknown half-fan criterion')
        indices = two_angle_indices(directions)
        relation = two_angle_relation(g, lookup, w, ring, indices)
        require(relation in ('<', '='), 'Cannot certify the specified two angles sum to at most pi')
        detail.update(two_angle_patch_indices=indices, two_angle_sum_relation_to_pi=relation)
    cuts = [[v, u] for u in ring] + [[w, ring[k]]]
    return dict(result='verified_half_fan_hypotheses', source=v, fan_vertex=w,
                equator=ring, patches=patches, directions=directions,
                criterion=criterion, **detail, slit_index=k, slit_vertex=ring[k],
                selected_cut_edges=cuts, sharpest_source_required=False,
                conclusion='The selected original-edge net is nonoverlapping by the written half-fan patch theorem.',
                scope='Exact hypotheses on this point or parameter region, invoking OCTA_HALF_FAN.md. This is not a proof of the general one-patch or adjacent-two-patch regime.')


def verify(spec):
    result = hypotheses(spec)
    require({edge(*e) for e in spec['cut_edges']} ==
            {edge(*e) for e in result['selected_cut_edges']},
            'Cuts disagree with the theorem-selected opening')
    return result


def audit_two_angle_failure(spec):
    """Check that both pole orientations fail the weaker two-angle test.

    This makes no assertion about the extension inequality or unfolding
    failure; the same octahedron may have a separately certified safe net.
    """
    g = Geometry(spec)
    sel = spec['selection']
    v, w, ring = sel['apex'], sel['antipode'], sel['equator']
    patches, directions, lookup = setup(g, v, w, ring)
    indices = two_angle_indices(directions)
    relations = [two_angle_relation(g, lookup, pole, ring, indices) for pole in (v, w)]
    require(relations == ['>', '>'], 'Both pole tests must be certified strictly above pi')
    order = verify_order(g, [(v, x) for x in range(6) if x != v])
    return dict(result='verified_two_angle_shortcut_failure', source=v, opposite=w,
                patches=patches, directions=directions, curvature_order=order,
                physical_patch_edges=[[ring[i], ring[(i+1) % 4]] for i in indices],
                pole_angle_sum_relations=relations,
                scope='Both orientations of this opposite pair fail the sufficient two-angle shortcut, even under H. This does not refute the extension inequality, the four-choice rule, or edge unfoldability.')


if __name__ == '__main__':
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--audit-two-angle-failure', action='store_true')
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 192))
    check = audit_two_angle_failure if args.audit_two_angle_failure else verify
    print(json.dumps(check(spec), indent=2))
