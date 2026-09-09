"""Replay partial covers and measure progress within a named parameter box.

Fractions use chart-parameter volume, not a measure on all polyhedron shapes.
Every cell labelled certified must pass the existing exact geometric verifier.
Unresolved cells remain explicit; their number is not a coverage percentage.
"""
from collections import Counter
from fractions import Fraction as F
import hashlib
import gzip
import json
from pathlib import Path
from n6.certify import require
from n6.cover import leaves,leaf_spec
from n6.polycert import verify as verify_leaf


def audit(cover):
    base=cover['geometry'];widths=[F(b)-F(a) for a,b in base['parameter_box']]
    counts=Counter();volumes=Counter();pairs=Counter();trees=set()
    for node,box,depth in leaves(cover):
        fraction=F(1)
        for (a,b),width in zip(box,widths):
            if width:fraction*=(F(b)-F(a))/width
        kind=node['kind']
        if kind=='certified':
            report=verify_leaf(leaf_spec(base,box,node))
            require(report['result']=='verified','Geometric replay failed')
            pairs.update(report['pairs']);trees.add(tuple(sorted(map(tuple,node['cuts']))))
        counts[kind]+=1;volumes[kind]+=fraction
    require(sum(volumes.values())==1,'Cells do not account for the full root box')
    return dict(result='verified_partial_region_coverage' if counts['unresolved'] else 'verified_complete_region_coverage',
                parameter_dimension=len(widths),certified_cells=counts['certified'],unresolved_cells=counts['unresolved'],
                certified_parameter_fraction=str(volumes['certified']),unresolved_parameter_fraction=str(volumes['unresolved']),
                distinct_cut_trees=len(trees),checked_face_pairs=dict(pairs),
                scope='Exact coverage of this named parameter box only. Fractions are chart-parameter volume, not progress toward a universal theorem. Unresolved cells may be split further.',
                boundary_scope='Closed certified cells include their boundaries. Unresolved cells and their boundaries are not claimed covered; volume ignores shared boundaries.')


def main():
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();raw=args.input.read_bytes()
    # Bind the report to exactly the bytes replayed, even if another search
    # replaces its saved file while this potentially long verification runs.
    cover=json.loads(gzip.decompress(raw) if args.input.suffix=='.gz' else raw)
    report=audit(cover)
    report['source_file']=args.input.name;report['source_sha256']=hashlib.sha256(raw).hexdigest()
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
