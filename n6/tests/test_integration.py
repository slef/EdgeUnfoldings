import itertools
import json
from pathlib import Path
import sys
import tempfile
import unittest
import networkx as nx
import numpy as np
import z3
from n6.encoding import Counterexample, export_smt2, tree_paths, atlas
from n6.query import nearstar_trees, run_bounded

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'durer_small_n'))
from octa import Octa, octa_structure
from adv_angle import score


class IntegrationTests(unittest.TestCase):
    def test_flat_facet_is_not_an_octahedron(self):
        p=np.array([[46,-100,-33],[-2,2,2],[-4,7,1],[-7,13,4],[6,-13,-5],[-1,1,0]])
        self.assertIsNone(octa_structure(p))
        from n6.sector_probe import setup
        self.assertIsNone(setup(p))

    def test_archive_sources_are_identical(self):
        manifest=json.loads((ROOT/'n6/archive_notes/manifest.json').read_text())
        digests=[m['sha256'] for arc in manifest for m in arc['members'] if m['path'].endswith('/unfolding.py') or m['path']=='unfolding.py']
        self.assertEqual(len(digests),2)
        self.assertEqual(*digests)

    def test_all_24_trees_have_nine_residual_pairs(self):
        ce=Counterexample(nx.octahedral_graph(),prune_vertex_fans=True)
        trees=list(nearstar_trees(ce))
        self.assertEqual(len({frozenset(map(frozenset,t.edges())) for t in trees}),24)
        paths=set()
        for t in trees:
            remaining=[p for p in tree_paths(t) if not set.intersection(*(set(ce.faces[f]) for f in p))]
            self.assertEqual(len(remaining),9)
            paths.update(remaining)
        self.assertEqual(len(paths),120)

    def test_census_has_all_seven_types(self):
        self.assertEqual([sum(len(g)==n for g in atlas()) for n in range(4,8)],[1,2,7,34])

    def test_corrected_far_angle_uses_actual_far_vertex(self):
        spec=json.loads((ROOT/'n6/results/d-lemma-counterexample.json').read_text())
        p=np.array([[float(q[0]) for q in pt] for pt in spec['coordinate_box']])
        tested=0
        for v in range(6):
            o=Octa(p,v)
            for i in range(4):
                j,jj=(i+1)%4,(i+2)%4
                sw=o.bW[j]+o.bWp[i]+o.bWp[j]+o.bW[jj]
                if sw>=np.pi:continue
                self.assertAlmostEqual(score(o,i,'i',False),o.aV[i]-sw,places=10)
                self.assertAlmostEqual(score(o,i,'jj',False),o.aVp[jj]-sw,places=10)
                tested+=1
        self.assertGreater(tested,0)

    def test_exporter_preserves_unsat(self):
        x=z3.Real('x');exprs=[x*x<0]
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'query.smt2';export_smt2(exprs,p)
            s=z3.SolverFor('QF_NRA');s.from_file(str(p))
            self.assertEqual(s.check(),z3.unsat)

    def test_hard_deadline_records_unresolved(self):
        with tempfile.TemporaryDirectory() as d:
            result=run_bounded(dict(output=str(Path(d)/'query'),family='nearstar',graph6=None,trees=0,
                                    no_prune=False,export_only=False,solver_ms=1000,wall_seconds=0.00001,memory_mb=256))
            self.assertEqual(result['result'],'wall_timeout')
            self.assertFalse(result['independent_proof_certificate'])


if __name__=='__main__':unittest.main()
