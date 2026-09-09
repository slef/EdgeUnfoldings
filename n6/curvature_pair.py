"""Exact hypotheses for the opposite-pole curvature sufficient theorem.

The geometric proof is in OCTA_TWO_SHARP_POLES.md. These interval checks do
not formally verify that proof or prove that every octahedron passes its test.
"""
import json
from pathlib import Path
from itertools import combinations
from n6.polycert import Geometry
from n6.curvature import angle_product,interval_angle_le,cmul,conjugate
from n6.regimes import curvature_pi
from n6.certify import require
from n6.intervals import I


def weighted_curvature_bound(sector_total, source_total):
    """K+2*J >= 2*pi; None means that interval signs do not decide it."""
    band=curvature_pi(source_total)
    if band in ('>','='):return True
    if band!='<':return None
    return interval_angle_le(cmul(source_total,source_total),conjugate(sector_total))


def verify(spec):
    g=Geometry(spec);claim=spec['curvature_pair']
    w,v,ring=claim['sector_vertex'],claim['source'],claim['equator']
    # Corner resolution is not a theorem hypothesis: only the octahedral
    # topology is needed. Avoid rejecting a valid threshold case merely due
    # to an unrelated unresolved patch corner.
    require(v!=w and len(set(ring))==len(ring)==4 and set(ring)|{v,w}==set(range(6)),'Invalid pole labels')
    wanted={frozenset((p,ring[i],ring[(i+1)%4])) for p in (v,w) for i in range(4)}
    require({frozenset(f) for f in g.faces}==wanted,'Wrong octahedral faces')
    W=angle_product(g.p,g.faces,g.h,w);V=angle_product(g.p,g.faces,g.h,v)
    require(interval_angle_le(W,(I(-1),-I(3).sqrt())) is True,'Sector curvature at least 120 degrees not certified')
    band=curvature_pi(V)
    if band in ('>','='):
        weighted='Source curvature at least pi already supplies 2*J >= 2*pi'
    else:
        require(band=='<','Source curvature band unresolved')
        # For 0<J<pi, V^2 has phase 2*pi-2*J in (0,2*pi).
        # Compare that angle to K, whose product is conjugate(W).
        require(weighted_curvature_bound(W,V) is True,'Weighted curvature inequality not certified')
        weighted='K >= 2*pi-2*J by exact angle-product ordering'
    return dict(result='verified_curvature_pair_hypotheses',sector_vertex=w,source=v,
                source_curvature_band=band,weighted_comparison=weighted,
                incident_angle_products={str(w):[x.pair() for x in W],str(v):[x.pair() for x in V]},
                candidate_slit_vertices=ring,
                conclusion='A shortest two-face source-to-sector path has an endpoint u with |sector--u| no greater than its length. Cutting star(source) plus sector--u gives a nonoverlapping net.',
                scope='Exact hypotheses on this point or region, invoking the written curvature-pair and exterior-sector theorems. No universal coverage claim and no certification of an arbitrarily selected net.')


def verify_central(spec):
    g=Geometry(spec)
    require(len(g.faces)==8 and all(len(f)==3 for f in g.faces),'Expected eight triangular facets')
    edges={frozenset(e) for f in g.faces for e in combinations(f,2)}
    require(all(sum(v in e for e in edges)==4 for v in range(6)),'Expected octahedral degrees')
    pairs=[(a,b) for a,b in combinations(range(6),2) if frozenset((a,b)) not in edges]
    require(len(pairs)==3,'Expected three opposite pairs')
    q=g.polynomial_points
    # Polynomial identities prove the symmetry over the entire parameter box.
    center=[q[pairs[0][0]][j]+q[pairs[0][1]][j] for j in range(3)]
    for a,b in pairs[1:]:
        for j in range(3):require((q[a][j]+q[b][j]-center[j]).is_zero(),'Opposite midpoints do not coincide identically')
    return dict(result='verified_central_octahedron_hypotheses',opposite_pairs=pairs,
                conclusion='The central-symmetry corollary proves some sharpest-source four-choice net nonoverlapping.',
                scope='Exact central-symmetry and convex-octahedron hypotheses over this point or parameter region, invoking the written universal proof. A specified selected net needs its own certificate.')


if __name__=='__main__':
    import argparse
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path);ap.add_argument('--central',action='store_true')
    args=ap.parse_args();spec=json.loads(args.certificate.read_text());set_precision(spec.get('suggested_fractional_bits',192))
    print(json.dumps((verify_central if args.central else verify)(spec),indent=2))
