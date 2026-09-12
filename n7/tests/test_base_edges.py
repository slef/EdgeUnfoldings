"""Finite verification of the auxiliary construction, separate from its proof."""
from fractions import Fraction as F
import itertools
import json
import unittest
import numpy as np
from n7.a992 import points_from_parameters,unfold
from n7.a992_exact import ROOT
from n7.base_edge_examples import RIGHT,AUX_CUT,AUX_FACES,extension_data,example_signs,replay

class BaseEdgeChecks(unittest.TestCase):
    def test_exact_examples_in_both_proved_branches(self):
        report=replay()
        self.assertEqual(report['exact_classes'],['converging','parallel'])
        self.assertEqual(report['strict_Left_overlaps'],2)
        self.assertEqual(report['strict_Right_residual_separators'],6)

    def test_divergent_obstruction_stays_outside_new_subcase(self):
        c=json.loads((ROOT/'results/a992-exact-counterexample.json').read_text())
        q=c['geometry']['parameters']
        self.assertEqual(extension_data(q)['classification'],'diverging')
        with self.assertRaises(ValueError):example_signs(q)

    def test_extension_preserves_actual_pair_placement(self):
        c=json.loads((ROOT/'results/a992-base-edge-examples.json').read_text())['examples'][0]
        q=c['geometry']['parameters'];data=extension_data(q)
        self.assertEqual((F(data['s']),F(data['t'])),(2,2))
        p=points_from_parameters(list(map(float,map(F,q))))
        p=np.vstack((p,np.array(list(map(float,map(F,data['x']))))))
        full=unfold(p,RIGHT);aux=unfold(p,AUX_CUT,AUX_FACES,4)
        # Aux W2 is x,2,3; the original face is 2,3,5 with 5 on segment 2x.
        s=float(F(data['s']));target=[aux[5][1],aux[5][2],(1-1/s)*aux[5][1]+aux[5][0]/s]
        for i,j in itertools.product(range(3),repeat=2):
            actual=float(np.sum((full[1][i]-full[6][j])**2))
            comparison=float(np.sum((aux[0][i]-target[j])**2))
            self.assertAlmostEqual(actual,comparison,delta=1e-10*max(1,actual,comparison))

if __name__=='__main__':unittest.main()
