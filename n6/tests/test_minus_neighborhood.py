import json
from pathlib import Path
import unittest
import z3
from n6.minus_pair import paired_trees,proof_progress
from n6.polycert import make_certificate,verify,point_spec,Geometry
from n6.minus_query import spatial_geometry,develop
from n6.minus_targeted import verify_audits
from n6.families import MINUS_FACES as FACES
from n6.intervals import set_precision

RESULTS=Path(__file__).resolve().parents[1]/'results'
def read(name):return json.loads((RESULTS/name).read_text())


class MinusNeighborhoodTests(unittest.TestCase):
    def tearDown(self):set_precision(80)

    def test_stable_classes_and_complete_partition(self):
        report=proof_progress();self.assertEqual(json.loads(json.dumps(report)),read('minus-pair-proof-progress.json'))
        self.assertEqual([c['id'] for c in report['classes'] if c['status']!='open'],[7,13,18,19,20,21,22])
        self.assertEqual(report['remaining_pairs_per_tree'],[6,6])
        self.assertEqual(report['remaining_failure_combinations'],36)
        self.assertEqual(sum(len(c['orbit']) for c in report['classes']),49)
        self.assertEqual(report['remaining_classes'],21)

    def test_theorem_witness_records_dependency_and_rejects_wrong_base(self):
        cert=read('minus-pair-neighborhood.certificate.json');report=verify(cert)
        self.assertEqual(report['pairs'],dict(vertex_fan=14,separating_edge=6,face_neighborhood=1))
        self.assertEqual(report['theorem_dependencies'][0]['theorem'],1)
        witness=next(w for w in cert['pair_witnesses'] if w['kind']=='face_neighborhood')
        witness['base']=4
        with self.assertRaisesRegex(ValueError,'direct neighbors'):verify(cert)

    def test_longer_path_cannot_use_the_face_neighborhood_theorem(self):
        p=[[0,0,0],[1,0,0],['1/2','-1/2',0],['1/2','1/2',0],
           ['1/2','-1/4',-1],['1/2','1/4',-1]]
        cert=make_certificate(point_spec(p,FACES,paired_trees()[0]['cuts']))
        index=next(i for i,w in enumerate(cert['pair_witnesses']) if w['faces']==[1,3])
        cert['pair_witnesses'][index]=dict(faces=[1,3],kind='face_neighborhood',base=0)
        with self.assertRaisesRegex(ValueError,'direct neighbors'):verify(cert)

    def test_query_chart_has_all_strict_original_supports(self):
        _,assertions=spatial_geometry()
        names=z3.Reals('c d e f r s h t k l')
        good=['8/5','3/10','-21/5','13/10','-29/5','0','3/5','-133/10','9/10','1']
        for height,expected in [('1',True),('-1',False)]:
            values=good.copy();values[-1]=height
            predicates=[z3.simplify(z3.substitute(a,*zip(names,map(z3.RealVal,values)))) for a in assertions]
            self.assertEqual(all(z3.is_true(a) for a in predicates),expected)
            c,d,e,f,r,s,h,t,k,l=values
            p=[[0,0,0],[1,0,0],[c,'-'+d,0],[e,f,0],[r,s,'-'+h],[t,k,str(-int(l))]]
            if expected:Geometry(point_spec(p,FACES,paired_trees()[0]['cuts']))
            else:
                with self.assertRaises(ValueError):Geometry(point_spec(p,FACES,paired_trees()[0]['cuts']))

    def test_query_development_keeps_the_quad_and_correct_hinge_side(self):
        p=[[0,0,0],[1,0,0],[1,-1,0],[0,1,0],[0,-1,-1],[0,1,-1]]
        placed,assertions=develop(p,{'hinges':[(0,6)]})
        self.assertEqual(placed[0],{v:p[v][:2] for v in FACES[0]})
        solver=z3.SolverFor('QF_NRA');solver.add(*assertions)
        self.assertEqual(solver.check(),z3.sat)
        x,y=placed[6][4]
        # Unfolding about the vertical BC edge sends P to (1+sqrt(2),-1).
        solver.add(z3.Or(y!=-1,x<=1,(x-1)*(x-1)!=2))
        self.assertEqual(solver.check(),z3.unsat)

    def test_all_eight_near_flat_audits_replay_without_joint_failure(self):
        report=verify_audits(read('minus-pair-targeted-audits.certificate.json'))
        self.assertEqual(len(report['outcomes']),8)
        self.assertTrue(all(row['verified_successes']>=1 for row in report['outcomes']))
        self.assertEqual(sum(row['verified_failures'] for row in report['outcomes']),5)


if __name__=='__main__':unittest.main()
