# Exact examples locating the convexity failures

13 September 2026. All coordinates below are rational. The companion
`exact_topological_audit.py` keeps the supplied face complex rather than
replacing it by its convex hull.

## A six-vertex counterexample in the paper's graph

Use the paper's vertex labels and coordinates

| Vertex | x | y | z |
| --- | ---: | ---: | ---: |
| A | -3000 | 0 | 0 |
| B | 0 | -100 | 0 |
| C | -1000 | 0 | 0 |
| D | 0 | 100 | 0 |
| E | -800 | -62 | 1 |
| F | -800 | 62 | 1 |

The original faces, coherently oriented, are

    DCBA, ABE, AEF, AFD, BCE, CFE, CDF.

This is an explicit rational instance of the obstruction in Theorem 5 and
Lemma 8 of the attached paper, not a new type of counterexample. Reflection
across y=0 exchanges B/D and E/F. For checking only, split the quadrilateral
along AC, giving the oriented triangles CBA and ADC. AC is **not** an
admissible original cut edge.

The exact checker verifies that all triangles have positive area, every
edge is paired with opposite orientation, each vertex link is a cycle,
the complex is connected with Euler characteristic two, and every pair of
triangles intersects only in its prescribed common edge or vertex. It also
checks all original hinges are nonflat and the original graph is
3-connected. Thus these are an embedded topologically convex polyhedron,
not merely a list of angle data or a self-intersecting immersion.

### The angle obstructions require no inverse trigonometry

Let theta be the minor angle BCD. The original quadrilateral is concave at C,
so its interior angle there is 2*pi-theta. Exact dot products show

    angle BCE > theta,
    angle AEB > 150 degrees,
    angle BEC > 150 degrees,
    angle CEF > 60 degrees.

For the first inequality, both cosines are positive, and comparison of
squared cosines proves it. For the two 150-degree bounds, the relevant dot
product d is negative and `4*d^2 > 3*|u|^2*|v|^2`. For the 60-degree bound,
the dot product is positive and `4*d^2 < |u|^2*|v|^2`. Every comparison is
between integers. Therefore

    interior_angle_C(ABCD) + angle BCE > 2*pi,
    angle AEB + angle BEC + angle CEF > 2*pi.

These are the paper's conditions (9) and (10). Reflection supplies the
corresponding condition at F. They imply negative curvature at C,E,F.
All original face angles at A,B,D are acute, and their degrees are at most
four, so their curvature is strictly positive. No vertex has zero curvature.

### Exhaust all cuts

For a connected edge unfolding of an embedded sphere, the cut graph cannot
contain a cycle. Since all six vertex curvatures are nonzero, every vertex
must belong to a nontrivial component of that forest. A negative-curvature
vertex cannot be a leaf: after one cut its face sector still exceeds 2*pi.
Only A,B,D can be leaves. Two nontrivial tree components would require at
least four distinct leaves, so the cut forest must be a single spanning tree.

There are exactly 224 spanning trees of the original eleven-edge graph.
The exact enumeration partitions them as follows:

| Obstruction, in this order | Trees excluded |
| --- | ---: |
| C, E, or F is a leaf | 194 |
| At least one of BC, CD is uncut | 26 |
| Overfull E or F sector between the remaining cuts | 4 |
| Total | 224 |

The second row follows because the triangle on an uncut BC or CD would
overlap the quadrilateral in a neighborhood of C. The last four cut sets are

    AE, BC, CD, CF, EF
    AE, BC, CD, DF, EF
    AF, BC, BE, CD, EF
    AF, BC, CD, CE, EF.

In the first two, E has cut degree two and its two cuts are EA and EF; the
uncut sector AEB+BEC+CEF exceeds a full turn. The last two are the reflection
at F. Hence every possible unfolding overlaps with positive area. Boundary
contact conventions do not change the conclusion.

### Why our minus-edge proof cannot be applied

The missing diagonal that would restore the octahedral graph is BD. Its
midpoint (0,0,0) is outside the original quadrilateral. It is therefore
not a flat hinge on this surface. The valid subdivision diagonal AC does
not restore the octahedral graph.

The old manuscript labels `(A,B,C,D,P,Q)` correspond to the paper labels
`(A,C,B,D,E,F)`. Under this relabeling the old proposed auxiliary diagonal
CD is exactly the invalid diagonal BD above. This identifies the failure
at the specific refinement step of `n6/PAIRED_POLE_RULE.md`.

## Why every concave quadrangular pyramid defeats the apex star

Let ABCD be any simple concave quadrilateral, reflex at C, and let P be an
apex outside its plane. Let theta in (0,pi) be the minor angle between CB
and CD, and let alpha=angle BCP and beta=angle PCD. The spherical triangle
inequality for the three edge directions gives alpha+beta>theta. Strictness
holds because P is outside the base plane. The full face-angle sum at C is

    (2*pi-theta) + alpha + beta > 2*pi.

Cutting PA,PB,PC,PD makes C a leaf and necessarily causes local overlap.
This refutes the existing cut rule for the whole concave-pyramid class;
it does not refute the existence of some other cut.

For the concrete example

    A=(0,0,0), B=(4,0,0), C=(1,1,0), D=(0,4,0), P=(0,0,2),

both side angles at C are obtuse, providing an especially short exact
negative-curvature check. In this example, cutting the Hamiltonian path

    D - A - B - C - P

does work. `n5_net_certificate.py` develops all faces with outward rational
intervals and finds a separating line for each of the fifteen pairs of
triangles. The base is subdivided along AC only for verification, and AC
remains uncut, so the result preserves the original quadrilateral.
This certifies one polyhedron, not a neighborhood or a universal pyramid rule.

## A triangular bipyramid where all three equator stars fail

Use equator A=(0,0,0), B=(10,0,0), C=(0,10,0) and poles

    P=(40,-40,1), Q=(-10,-20,-5).

Its six oriented faces are PAB,PBC,PCA,QBA,QCB,QAC. The two tetrahedral caps
are on opposite sides of the equator plane and give an embedded sphere.
The checker also verifies all fifteen triangle-pair intersections exactly.

At A the two P-face angles sum to pi: their cosines are opposite. Both
Q-face angles are obtuse. Thus A has negative curvature. At B, exact dot
products give

    angle ABP > 120 degrees,
    angle CBP > 150 degrees,
    angle CBQ = 90 degrees,
    angle QBA > 0.

The total exceeds 360 degrees, so B also has negative curvature. The only
vertices adjacent to all four other vertices are A,B,C. The star at A
leaves negative-curvature B as a leaf; the star at B leaves A as a leaf;
the star at C leaves both. All three stars fail.

This is a counterexample to a proposed **star-selection strategy**, not an
ununfoldable five-vertex polyhedron. No claim about all its spanning trees
is made by this certificate.

## An ambient Radon failure with positive curvature

The example and proof in [POSITIVE_CURVATURE.md](POSITIVE_CURVATURE.md) use
two nested caps on the same side of ABC. All its intrinsic curvatures are
positive, and it is isometric face by face to a convex reflected bipyramid.
Nevertheless, its actual pole segment misses the equator plane, and one
pole lies inside the tetrahedron formed by the other four vertices.

This fourth exact check is included to distinguish three issues: topology,
intrinsic curvature, and the particular spatial convexity statements used
in the current Lean proof.
