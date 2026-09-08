from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import unittest
from n6.cover import verify
from n6.polycert import Geometry,propose_pairs,verify as verify_leaf
from n6.trees import degree_four_stars


def example():
    spec=json.loads((Path(__file__).resolve().parents[1]/'results/prism-region.certificate.json').read_text())
    leaf=dict(kind='certified',cuts=spec['cut_edges'],pairs=spec.pop('pair_witnesses'))
    middle=str(sum(map(F,spec['parameter_box'][0]))/2)
    return dict(schema='n6-binary-region-cover-v1',geometry=spec,
                tree=dict(kind='split',axis=0,value=middle,children=[deepcopy(leaf),deepcopy(leaf)]))


class RegionCoverTests(unittest.TestCase):
    def test_shared_development_cache_survives_switching_cut_trees(self):
        spec=example()['geometry']
        spec['parameter_box']=[[str((F(a)+F(b))/2)]*2 for a,b in spec['parameter_box']]
        g=Geometry(spec);checked=0
        for tree in degree_four_stars(g.faces):
            g.adj={i:[] for i in range(len(g.faces))}
            for a,b in tree['hinges']:g.adj[a].append(b);g.adj[b].append(a)
            try:pairs=propose_pairs(g)
            except ValueError:continue
            cert={**spec,'cut_edges':tree['cuts'],'pair_witnesses':pairs}
            self.assertEqual(verify_leaf(cert)['result'],'verified');checked+=1
        self.assertGreater(checked,1)

    def test_two_closed_children_cover_parent_including_interface(self):
        report=verify(example())
        self.assertEqual(report['leaves'],2)
        self.assertEqual(report['parameter_dimension'],9)
        self.assertEqual(sum(report['checked_face_pairs'].values()),30)

    def test_missing_child_cannot_be_accepted_as_complete(self):
        cert=example();cert['tree']['children'].pop()
        with self.assertRaisesRegex(ValueError,'exactly two'):verify(cert)

    def test_split_outside_parent_is_rejected(self):
        cert=example();cert['tree']['value']='10'
        with self.assertRaisesRegex(ValueError,'strictly interior'):verify(cert)

    def test_unresolved_leaf_prevents_proof_verdict(self):
        cert=example();cert['tree']['children'][0]=dict(kind='unresolved',reason='timeout')
        with self.assertRaisesRegex(ValueError,'incomplete'):verify(cert)

    def test_full_geometric_certificate_is_required_at_each_leaf(self):
        cert=example();cert['tree']['children'][1]['pairs'].pop()
        with self.assertRaisesRegex(ValueError,'Missing face pairs'):verify(cert)


if __name__=='__main__':unittest.main()
