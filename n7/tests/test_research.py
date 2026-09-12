import itertools as it
import json
from fractions import Fraction
from html.parser import HTMLParser
from pathlib import Path
import unittest
from urllib.parse import unquote,urlsplit
import networkx as nx
from n7.catalogue import census,cofacial_candidates,facets,pair_audit
from n7.checks import acute_box,canonical_pattern,patch_patterns,plantri_comparison,verify_catalogue
from n7.build_overview import candidate,graph_positions
ROOT=Path(__file__).resolve().parents[1]

class Page(HTMLParser):
    def __init__(self,text):
        super().__init__();self.ids=[];self.links=[];self.graphs=[];self.feed(text)
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if 'id' in a:self.ids.append(a['id'])
        if 'href' in a:self.links.append(a['href'])
        if 'src' in a:self.links.append(a['src'])
        if tag=='article' and 'graph-card' in a.get('class',''):self.graphs.append(a)

class ResearchChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.data=json.loads((ROOT/'results/catalogue.json').read_text())
    def test_complete_census_and_independent_generator(self):
        raw=census()
        self.assertEqual(len(raw['graphs']),34)
        self.assertEqual(raw['edge_histogram'],{11:2,12:8,13:11,14:8,15:5})
        report=plantri_comparison(self.data,ROOT/'results/plantri.g6')
        self.assertEqual(json.loads(json.dumps(report)),json.loads((ROOT/'results/plantri-comparison.json').read_text()))
        self.assertEqual(report['output_count'],34)
    def test_same_degree_sequence_does_not_merge_distinct_graphs(self):
        rows=[r for r in self.data['graphs'] if r['degrees']==[5,4,4,4,3,3,3]]
        self.assertEqual(len(rows),5)
        for a,b in it.combinations(rows,2):self.assertFalse(nx.is_isomorphic(nx.Graph(a['edges']),nx.Graph(b['edges'])))
    def test_saved_witnesses_and_independent_tree_count(self):
        checked=verify_catalogue(self.data)
        self.assertEqual(checked,json.loads((ROOT/'results/validation.json').read_text()))
        self.assertEqual(checked['all_tree_count_independently_matched'],25942)
        self.assertEqual((checked['solved_graphs'],checked['open_graphs']),(10,24))
    def test_invalid_cofacial_claim_is_rejected(self):
        r=next(r for r in self.data['graphs'] if r['atlas_index']==1212);g=nx.Graph(r['edges'])
        with self.assertRaises(ValueError):pair_audit(g,r['facets'],r['all_tree_scan']['best']['cut'],{'source':5,'changed_faces':[]})
        r=next(r for r in self.data['graphs'] if r['atlas_index']==992);g=nx.Graph(r['edges']);c=r['cofacial_candidates'][0]
        with self.assertRaises(ValueError):pair_audit(g,r['facets'],c['cut'],dict(c,changed_faces=[]))
    def test_single_pair_target_is_still_open(self):
        r=next(r for r in self.data['graphs'] if r['atlas_index']==992);c=r['cofacial_candidates'][0]
        self.assertEqual(r['status'],'open');self.assertEqual(c['source'],3)
        self.assertEqual((c['audit']['safe_count'],c['audit']['total_pairs']),(20,21))
        self.assertEqual(c['audit']['unresolved'],[{'faces':[0,1],'path':[0,5,2,1]}])
        triple=next(r for r in self.data['graphs'] if r['atlas_index']==1005)
        self.assertEqual(len(candidate(triple)['changed_faces']),3)
        self.assertEqual(triple['status'],'open')
    def test_pattern_partition_and_proved_subfamilies(self):
        p=patch_patterns();self.assertEqual((p['labelled_count'],p['class_count'],p['proved_classes']),(121,15,7))
        self.assertEqual(p,json.loads((ROOT/'results/patch-patterns.json').read_text()))
        self.assertEqual(canonical_pattern('FCBCC'),'BCCFC')
        self.assertFalse(any('FFFFF' in r['members'] or 'BBBBB' in r['members'] for r in p['classes']))
    def test_exact_box_and_too_large_box_rejection(self):
        c=acute_box();saved=json.loads((ROOT/'results/acute-bipyramid-box.json').read_text())
        self.assertEqual(json.loads(json.dumps(c)),saved)
        self.assertEqual((c['support_count'],c['corner_count']),(40,30))
        self.assertGreater(Fraction(c['minimum_support_lower_bound']),0)
        self.assertGreater(Fraction(c['minimum_corner_lower_bound']),0)
        with self.assertRaises(ValueError):acute_box(Fraction(1,2))
    def test_every_graph_drawn_and_local_links_resolve(self):
        pages={p.name:Page(p.read_text()) for p in ROOT.glob('*.html')}
        overview=pages['index.html'];self.assertEqual(len(overview.graphs),34)
        self.assertEqual({g['id'] for g in overview.graphs},{r['id'] for r in self.data['graphs']})
        for name,page in pages.items():
            self.assertEqual(len(page.ids),len(set(page.ids)),name)
            for link in page.links:
                u=urlsplit(link)
                if u.scheme or u.netloc:continue
                path=(ROOT/unquote(u.path)) if u.path else ROOT/name
                self.assertTrue(path.is_file(),(name,link))
                if u.fragment and path.suffix=='.html':self.assertIn(unquote(u.fragment),pages[path.name].ids,(name,link))
    def test_diagrams_have_no_crossings(self):
        def orient(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
        for r in self.data['graphs']:
            pos=graph_positions(r,candidate(r))
            for (a,b),(c,d) in it.combinations(r['edges'],2):
                if len({a,b,c,d})<4:continue
                crossing=orient(pos[a],pos[b],pos[c])*orient(pos[a],pos[b],pos[d])<-1e-6 and orient(pos[c],pos[d],pos[a])*orient(pos[c],pos[d],pos[b])<-1e-6
                self.assertFalse(crossing,r['id'])

if __name__=='__main__':unittest.main()
