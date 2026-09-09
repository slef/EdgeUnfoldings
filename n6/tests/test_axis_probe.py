import json
from pathlib import Path
import unittest
import numpy as np
from n6.axis_probe import quantities,pack,points,Octa

class AxisProbeTests(unittest.TestCase):
    def test_coordinate_search_retains_the_certified_orientation(self):
        cert=json.loads((Path(__file__).resolve().parents[1]/'results/caseB-apex-entry.certificate.json').read_text())
        P=np.array([[float(c[0][0]) for c in row] for row in cert['coordinate_polynomials']])
        o=Octa(P,0)
        for slit in (0,3):
            x=pack(o,slit);q=quantities(x);rebuilt=Octa(points(x),0)
            np.testing.assert_allclose(2*np.pi-q['totals'],[rebuilt.kv,rebuilt.kw,*rebuilt.ku],atol=2e-12)
            self.assertEqual(int(np.argmax(rebuilt.ku)),slit)
            self.assertGreater(q['support'].min(),0)
            if slit==0:
                self.assertLess(q['angle_target'],0)
                self.assertGreater(q['apex_entry'][0],0)
                self.assertGreater(q['far_entry'][0],0)
                self.assertLess(q['apex_entry'][1],0)
                self.assertLess(q['far_entry'][1],0)

if __name__=='__main__':unittest.main()
