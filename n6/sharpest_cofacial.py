"""Exact counterexample to keeping only the sharpest source's two cofacial routes.

This does not refute the four-route family or edge unfoldability. Two other
original near-stars and the cap rule's prescribed tree are independently safe.
"""
from fractions import Fraction as F
from pathlib import Path
import json

from n6.certify import require
from n6.curvature import interval_angle_le
from n6.families import PRISM_FACES, PRISM_CUTS, prism_region, center_parameters
from n6.flat_octahedron import curvature_bands
from n6.polycert import Geometry, make_certificate, make_overlap, verify, verify_overlap
from n6.prism_angle_rule import select as angle_select
from n6.prism_paths import polygon_angle_product
from n6.trees import quadrilateral_path_stars

PARAMETERS = ('-7', '1', '-1/40', '1/50', '1/8', '4', '40', '1/20', '22')
FAILURE_PAIRS = {2: (0, 3), 4: (3, 4)}


def specification(family=False, cuts=PRISM_CUTS):
    width = F(1, 10**10) if family else F(0)
    box = [[str(F(q)-width), str(F(q)+width)] for q in PARAMETERS]
    return center_parameters(prism_region(box, cuts))


def check(family=False, output=None):
    spec = specification(family)
    g = Geometry(spec)
    products = {v: polygon_angle_product(g, v) for v in range(6)}
    comparisons = {}
    for v in range(6):
        if v == 1:
            continue
        forward = interval_angle_le(products[1], products[v])
        backward = interval_angle_le(products[v], products[1])
        require(forward is True and backward is False,
                'Source 1 is not certified strictly sharper than every other vertex')
        comparisons[str(v)] = dict(source_1_angle_sum_strictly_smaller=True)
    bands = curvature_bands(g)
    require(bands[1] == '>', 'Source 1 is not certified above pi')
    report = dict(result='verified_sharpest_source_both_cofacial_routes_fail',
                  strictly_sharpest_source=1, curvature_comparisons_with_pi=bands,
                  strict_source_comparisons=comparisons, parameter_dimension=9,
                  positive_parameter_width=family, failed_routes=[], successful_routes=[],
                  scope='Both cofacial routes at the unique sharpest vertex fail on this explicit point or open parameter neighborhood. The other source and the cap rule unfold it; no claim against edge unfoldability or the four-route family.')
    suffix = '-family' if family else ''
    for tree in quadrilateral_path_stars(PRISM_FACES):
        source, slit = tree['apex'], tree['slit_vertex']
        shape = {**spec, 'cut_edges': [list(e) for e in tree['cuts']]}
        if source == 1:
            pair = FAILURE_PAIRS[slit]
            cert = make_overlap(shape, *pair)
            result = dict(source=source, slit=slit, overlap_faces=list(pair),
                          exact_replay=verify_overlap(cert))
            group, kind = 'failed_routes', 'failure'
        else:
            cert = make_certificate(shape)
            result = dict(source=source, slit=slit, exact_replay=verify(cert))
            group, kind = 'successful_routes', 'success'
        name = f'prism-sharpest-cofacial-{kind}-source-{source}-slit-{slit}{suffix}.certificate.json'
        if output:
            (output/name).write_text(json.dumps(cert, indent=2)+'\n')
        result['certificate_file'] = name
        report[group].append(result)
    require(len(report['failed_routes']) == len(report['successful_routes']) == 2,
            'Expected both original routes at each of the two cofacial sources')
    selected = angle_select(spec)
    cert = selected.pop('certificate')
    name = 'prism-sharpest-cofacial-cap-success'+suffix+'.certificate.json'
    if output:
        (output/name).write_text(json.dumps(cert, indent=2)+'\n')
    selected['certificate_file'] = name
    report['cap_rule_prescribed_success'] = selected
    return report


def main():
    from n6.intervals import set_precision
    set_precision(240)
    root = Path(__file__).parent/'results'
    report = dict(result='verified_sharpest_cofacial_counterexample_and_family',
                  point=check(False, root), family=check(True, root))
    (root/'prism-sharpest-cofacial.verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Point and nine-parameter neighborhood verified: both sharpest-source routes overlap; both other-source routes and the cap rule are safe.')


if __name__ == '__main__':
    main()
