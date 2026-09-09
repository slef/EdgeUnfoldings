from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import unittest
from n6.cover import verify,summary,merge_covers
from n6.polycert import Geometry,propose_pairs,verify as verify_leaf
from n6.trees import degree_four_stars


def example():
    spec=json.loads((Path(__file__).resolve().parents[1]/'results/prism-region.certificate.json').read_text())
    leaf=dict(kind='certified',cuts=spec['cut_edges'],pairs=spec.pop('pair_witnesses'))
    middle=str(sum(map(F,spec['parameter_box'][0]))/2)
    return dict(schema='n6-binary-region-cover-v1',geometry=spec,
                tree=dict(kind='split',axis=0,value=middle,children=[deepcopy(leaf),deepcopy(leaf)]))


class RegionCoverTests(unittest.TestCase):
    def test_complementary_partial_covers_include_the_shared_boundary(self):
        a=example();b=example()
        a['tree']['children'][1]=dict(kind='unresolved')
        b['tree']['children'][0]=dict(kind='unresolved')
        result=merge_covers([a,b])
        self.assertEqual(summary(result)['parameter_volume_fractions'],{'certified':'1'})
        self.assertEqual(verify(result)['leaves'],2)

    def test_merge_preserves_unresolved_cells_and_rejects_different_roots(self):
        a=example();a['tree']['children'][1]=dict(kind='unresolved')
        result=merge_covers([a,a])
        with self.assertRaisesRegex(ValueError,'incomplete'):verify(result)
        b=example();b['geometry']['parameter_box'][0][0]='-1/1000'
        with self.assertRaisesRegex(ValueError,'different root'):merge_covers([a,b])

    def test_planar_projection_keeps_its_exact_linear_correlation(self):
        spec=json.loads((Path(__file__).resolve().parents[1]/'results/minus-quadrupled-cover.region.json').read_text())
        spec['parameter_box']=[['-1/32','1/32'] for _ in spec['parameter_box']]
        g=Geometry(spec)
        for a,b in ((0,2),(2,0)):
            _,height=g.projection(a,b,1)
            delta=height-g.box[1]
            self.assertEqual((delta.lo,delta.hi),(1,1))

    def test_leaf_counts_do_not_stand_in_for_parameter_volume(self):
        cert=example();lo,hi=map(F,cert['geometry']['parameter_box'][0])
        cert['tree']['value']=str(lo+(hi-lo)/4)
        cert['tree']['children'][1]=dict(kind='unresolved')
        report=summary(cert)
        self.assertEqual(report['certified'],report['unresolved'])
        self.assertEqual(report['parameter_volume_fractions'],{'certified':'1/4','unresolved':'3/4'})

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
