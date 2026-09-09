# The archive sector route: precise finite reduction

This is a sufficient route to an edge unfolding, complementary to the proposed
sharpest-apex rule. It does not prove that a suitable choice always exists.

## A shortest antipodal path crosses just two faces

For a strictly convex octahedron, let v,w be nonadjacent vertices and label the
four other vertices cyclically. Every shortest surface path from v to w lies
in `V_i union W_i` for some equator edge, crossing that edge in its relative
interior. Consequently its length is the minimum of the valid straight
two-face developments for the four equator edges.

Proof. A shortest path cannot pass through an intermediate polytope vertex:
the angles on its two sides would both need to be at least pi, whereas their
sum is strictly less than `2 pi`. It also cannot cross an edge incident to v
at an interior point x. The edge segment vx has exactly the Euclidean chord
length, so replacing the prefix by vx strictly shortens any different prefix.
Equality would force the prefix itself to be that straight edge segment; a
geodesic cannot follow an edge and then turn away at an interior edge point,
where the surface is locally Euclidean. The same argument applied to the
suffix excludes crossings of edges incident to w.

The path therefore starts inside a face V_i and can leave it only across its
equator edge. It then enters W_i. It cannot exit through a w-edge, and a
straight segment inside the triangle W_i cannot cross the same equator edge
twice. It must end at w. This proves the assertion, including possible ties
between different shortest paths. The same reasoning applies to a strictly
convex triangulated bipyramid with any number of equator vertices.

## Turning that path into an original-edge cut

Choose a shortest two-face path of length L crossing edge ab. In its developed
quadrilateral, choose u=a or u=b and put

```
r=|wu|,    gamma=angle(v,w,u),    kappa_w=curvature at w.
```

The sufficient conditions retained from the archive are

```
r <= L,    gamma <= kappa_w.
```

The external input is the exterior-sector theorem for star unfoldings: the
closed circular sector at a vertex, between its two source images and with
radius equal to source distance, has interior disjoint from the star unfolding.
Its angle is the vertex curvature. See Aronov–O'Rourke, Section 8.1 and
Theorem 9.1, [Nonoverlap of the star unfolding](https://link.springer.com/content/pdf/10.1007/BF02293047.pdf).

Cut the four shortest edge paths from v to its neighbours and the chosen
shortest path to w. The latter splits the developed quadrilateral into the
triangles `wuv` and the triangle using the other endpoint of ab. Cutting wu
frees the first triangle. Rotating it about w to the other copy of the shortest
path closes that nonedge cut. The moved triangle fits the exterior sector:
its two non-w vertices have radii at most L and its angular extent is gamma.
Its angular extent is below pi, so its whole convex hull lies in the appropriate
subsector and disk. The remaining cuts are exactly `star(v) union {wu}`.
The formerly split triangular facets rejoin along their original base edge.

For a vertex source or a tie between shortest paths, take sources approaching v
along the chosen shortest path. The paths to the four neighbours converge to
their unique Euclidean edge segments; a shortest path to w continues along the
chosen path. The star developments and their exterior sectors converge. A
positive-area overlap of nondegenerate limiting faces would persist nearby,
so the limiting sector argument still permits boundary contact. These limiting
details do not turn a numerically chosen path into a certificate: its shortest
path and sector inequalities must still be proved.

## The angular test is automatic at a globally sharpest w

If w has maximum curvature among the six vertices, `kappa_w>=2 pi/3`.
The convex-vertex cone inequality gives each incident face angle
`omega_i<=pi-kappa_w/2<=kappa_w`. The shortest path direction lies within
the angle omega_i of W_i, so either endpoint has `gamma<=kappa_w`.
Only the radial test remains for this particular strategy.

The radial test can fail for every neighbour of a globally sharpest w. An exact
example is `v=(499,499,1)`, `w=(0,0,-10000)`, and equator vertices
`(1000,0,0)`, `(0,1000,0)`, `(-1000,0,0)`, `(0,-1000,0)`. The checker certifies
w's curvature ranking and a valid two-face path shorter than every w-neighbour
edge. The true shortest path is at most that long, so none of those edges can
pass the radial test.

```
python3 -m n6.sector_audit n6/results/sector-sharpest-radial-failure.certificate.json
```

This refutes only the strategy fixing the sector vertex to a globally sharpest
w. There is still no proof that some oriented antipodal pair always passes both
sector tests. The archive's finite searches and `sector_probe.py` must retain
this distinction. The universal obligation is existence of a choice, not
further verification of the sufficient implication itself.
