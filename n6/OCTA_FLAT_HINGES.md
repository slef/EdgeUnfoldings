# The octahedral proof allows flat auxiliary hinges

11 September 2026. Written extension with a spherical-link and dependency
audit. Independent mathematical review is still needed; this is not formal
verification. No numerical experiment is a premise.

## Statement and consequences

Let a three-dimensional convex polytope have six genuine vertices. Suppose
its boundary can be triangulated, without adding vertices, into the eight
nondegenerate triangles of the octahedron graph. Some auxiliary edges may
be flat diagonals inside original quadrilateral faces.

The selected octahedron theorem, its source-choice extension, and the
weighted slit threshold continue to hold on this triangulated surface.
All six vertices must remain genuine vertices of the original solid, so
their curvatures are strictly positive; zero-curvature inserted vertices
are not covered. Only the auxiliary edge dihedrals may be flat.

Whenever the five chosen cuts are original edges, the resulting net is an
original-edge unfolding of the original polygonal facets.

Consequently:

1. **Both remaining nonsimplicial types unfold if all six curvatures are
   at most pi, including equality.** Use the same four minus-edge candidates
   or six prism candidates as before, with their original-edge R choices.
2. For either type, any original degree-four source v with curvature
   **at least pi** and any original fifth edge wc satisfying
   **2*kappa_c+kappa_w>=pi** give a safe fixed net. Here w is opposite v
   in the octahedral triangulation. Both equalities are included.

This advances the original [strictly-low theorem](NONSIMPLICIAL_LOW_CURVATURE.md)
without claiming that arbitrary small perturbations preserve a boundary
curvature. It also gives explicit families above the curvature boundary.
The full n=6 theorem remains open; a remaining shape must have maximum
curvature strictly greater than pi and fail the additional original-tree
criteria. The whole-type tally remains 5/7.

## 1. The spherical-link bound holds on the closed link

At a genuine vertex p of a three-dimensional convex polytope, the link K
is a geodesically convex spherical polygon of positive area in an open
hemisphere. A flat auxiliary edge only subdivides a side of K by an
additional point on the same great-circle arc. It does not change the
polygon, its perimeter Gamma, or its area.

Let a be an edge direction, including such a subdivision point, and q
any direction in **the closed polygon K**. Then

    Gamma > 2*distance(a,q).                         (1)

Moreover, if an incident boundary side ab of length omega is removed,

    Gamma-omega > distance(a,q).                     (2)

These are the same strict estimates used by Lemma L. We no longer need
the direction of an opposite vertex to lie strictly inside the link.
In a quadrilateral face it can lie on a link side.

To prove (1), if q!=a, extend the short great-circle segment from a through
q to a boundary point c, with distance(a,c)>=distance(a,q). All distances
are below pi because K lies in an open hemisphere. The two boundary paths
from a to c each have length at least their unique shortest arc. They
cannot both be that same shortest arc: that would give K zero area.
Their total is therefore strictly greater than 2*distance(a,c). The case
q=a is immediate from Gamma>0.

For (2), choose c on the boundary path remaining after ab is removed.
An interior ray cannot exit through the open side incident to its starting
point. If the ray runs along ab and q is on that side, choose c=b; if it
continues along further collinear side subdivisions, choose its later
boundary endpoint, which is on the remaining path. These choices always
have distance(a,c)>=distance(a,q).

If c!=b, the remaining path from a to b through c has length at least
distance(a,c)+distance(c,b)>distance(a,q). If c=b, that remaining path
has length strictly greater than the shortest arc ab: equality would make
the whole polygon degenerate with zero area. Again (2) follows. This also
handles collinear boundary subdivision points and an endpoint q=b.

The usual face-angle bound omega<=Gamma/2 remains valid by the two boundary
paths between the endpoints of that side. Every triangular face angle is
positive and below pi; coplanarity across a different edge does not alter it.

## 2. Dependency audit of the octahedral proof

The only stricter three-dimensional assertion needing replacement was
that the opposite-vertex direction is interior to each spherical link.
It is always in the closed tangent cone; Section 1 supplies precisely
the required strict bounds there. The rest of the proof uses:

| Step | Facts needed, still valid with flat hinges |
| --- | --- |
| Shared-vertex pairs | Positive triangle angles summing to 2*pi-kappa at a genuine vertex, with kappa>0 |
| Through-fan Lemma L | The strict link bounds (1)-(2), the triangle inequality for directions, and the cosine law |
| Across-slit Lemma L | Positive slit curvature, patch-angle sums, and the R or weighted-threshold separator |
| Finite-cut containment | Nondegenerate triangles glued on opposite sides of their common base, local safety, and shared uncut vertices |
| Pole-angle contradiction | (1) at the source and a nonobtuse supporting-line argument, including equality |
| Equal-length contradiction | Two copies of one edge have equal lengths, the cone bound, Gauss--Bonnet, and all curvatures<=pi |
| Case A | The no-wrap curvature inequality, actual triangle edge lengths, and the [planar apex-cone argument](CASE_A_CONES.md) |
| Base-cone branch | Planar angle sums and convex sectors; no dihedral-angle condition |
| Small-fan closed curve | The same local safety, positive curvature gaps, nondegenerate triangles, and the resulting hexagon angle sum |
| Interior-hinge reduction | Actual uncut adjacency and the explicitly retained local pair premises |

Strict convexity across every triangulation edge is not used in any of
these steps. The positive curvature gaps and strict local slit-boundary
separator remain strict by Section 1 and the unchanged determinant proof.
Thus the auxiliary closed curve and hexagon have the same boundary audit
as in LEMMA_F_CHORD.md and OCTA_SLIT_THRESHOLD.md. The local-safe all-low
extension may instead use its already-proved auxiliary shrink at contacts.

In particular this is not an appeal to continuity of a strict inequality
from nearby solids. The inequalities and planar proofs apply directly to
the boundary triangulation at hand.

## 3. Recover the original polygonal faces

Adding CD to the minus-edge quadrilateral, or 05 and 24 to the prism
quadrilaterals, gives the unique octahedral completion described in
NONSIMPLICIAL_LOW_CURVATURE.md. The diagonals split strictly convex
quadrilaterals into nondegenerate triangles. The six original vertices
remain genuine vertices; their face-angle sums are unchanged by the split.

For the all-low minus-edge family, choose A or B as source and its opposite
as fan center. All fifth edges are original. Every maximum-curvature equator
choice now works directly, including ties; no fixed-tree subsequence is
needed. Four candidates at a fixed one of these sources suffice.

For the all-low prism family, the two original degree-four sources 1 and 3
have forbidden fifth endpoints 0 and 4. The same cross-ranking argument
ensures at least one source has an allowed maximum. Each allowed tied
maximum gives a safe net directly. There are six original candidates.

For the higher-curvature sufficient rule, require the chosen source to
have original degree four and the fifth cut to be original. Apply the
weighted threshold theorem directly to the flat triangulation. This checks
the actual specified tree, rather than existence among an unknown choice.

In each application every artificial diagonal stays uncut. The developed
triangles on its two sides remain coplanar and form exactly their original
quadrilateral. If two original polygonal faces had positive-area overlap,
an interior point avoiding the finitely many diagonals would lie in two
triangle interiors. That contradicts the triangulated net's nonoverlap.
Boundary touching is allowed.

## Exact scope of the implementation

`flat_octahedron.py` checks the original strict polygonal facets, unique
octahedral diagonal completion, positive geometry, original cut tree, and
the stated curvature predicates. It does not weaken `polycert.Geometry`'s
strict-facet checker or treat a triangulated coplanar facet as a strict
triangular hull. Its conclusions invoke this written theorem.

The exact pi examples have three incident 60-degree original facet angles
at a degree-three vertex. A rational squared-cosine test recognizes those
angles and their exact sum, rather than declaring an interval containing
pi to be equality. Unrecognized or unresolved comparisons remain rejected.
Independent all-original-face-pair certificates provide separate checks.
