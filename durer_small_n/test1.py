import numpy as np, time
from unfold import Polytope
np.random.seed(0)
# regular tetrahedron
T = np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)
p = Polytope(T); pen = p.penetrations()
print("tetra: trees", len(p.trees()), "good", int((pen<=0).sum()))
# regular octahedron
O = np.array([[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]],float)
t=time.time(); p = Polytope(O); pen = p.penetrations()
print("octa: trees", len(p.trees()), "good", int((pen<=0).sum()), "time", time.time()-t)
# flat tetrahedron: should have overlapping path unfoldings
F = np.array([[0,0,0],[1,0,0],[0.5,0.9,0],[0.5,0.3,0.01]],float)
p = Polytope(F); pen = p.penetrations()
print("flat tetra: trees", len(p.trees()), "good", int((pen<=0).sum()))
# regular icosahedron-ish? skip. Regular pentagonal bipyramid
c = [[np.cos(2*np.pi*k/5), np.sin(2*np.pi*k/5), 0] for k in range(5)]
B = np.array(c+[[0,0,1],[0,0,-1]],float)
t=time.time(); p = Polytope(B); pen = p.penetrations()
print("pent bipyr: trees", len(p.trees()), "good", int((pen<=0).sum()), "time", time.time()-t)
