# Both remaining nonsimplicial types: the strictly low-curvature family

11 September 2026. Written geometric proof using the source-choice theorem
in [OCTA_SOURCE_CHOICE.md](OCTA_SOURCE_CHOICE.md). Independent review is still
needed. This is an entire shape family, not a numerical inference or a
percentage of the realization space.

## The theorem and its strict boundary

Every convex six-vertex polytope of either of the two remaining types has
a nonoverlapping original-edge unfolding if

    kappa_x < pi for all six vertices x.

The two types are an octahedron minus one edge (one quadrilateral face)
and a triangular prism with one diagonal (two quadrilateral faces).

The strict inequality preserves this condition under small perturbations.
This note does **not** include the boundary where the maximum curvature
equals pi, nor shapes with a greater maximum curvature. Those remain
separate obligations for these types. The full n=6 theorem is not claimed.

## 1. Octahedron minus one edge

Use the existing labels with quadrilateral A-C-B-D, and the two vertices
P,Q outside its plane. The original edges are

    AC, AD, AP, AQ, BC, BD, BP, BQ, CP, DQ, PQ.

The missing octahedral edge is CD. Adding that diagonal triangulates the
quadrilateral and gives the octahedron graph. Its opposite pairs include
A,B. Neither A nor B is incident to CD.

Keep v=A and w=B in nearby strict octahedral refinements. Every original
curvature is below pi, so all nearby curvatures remain below pi. By the
source-choice theorem, choose a maximum-curvature vertex c among C,D,P,Q:

    star(A) together with Bc

is a successful net of each refinement. Every one of these five cuts is
an original edge. In particular CD is always a hinge, not a cut.

There are four possible c. Pass to a subsequence with one fixed choice.
The limiting tree unfolds the original polytope, by Section 4 below.
Thus the four original-edge extensions of star(A) include a successful
tree. The reflected statement with source B also follows.

An explicit algorithm may try those four trees. It may discard choices
that are not maximum-curvature equator vertices of the original solid:
continuity ensures that the successful subsequence limit is a maximum.
At ties, this argument proves existence among the tied choices, not that
every tied limiting tree works.

## 2. Prism with one diagonal

Use the repository labels with faces

    (0,2,1), (0,3,5,2), (0,1,3),
    (1,2,5,4), (1,4,3), (3,4,5).

The original degree-four vertices are 1 and 3. Add diagonals 05 and 24 to
the two quadrilaterals. This gives the octahedron graph with opposite
pairs (1,5), (3,2), (0,4). The two possible degree-four sources have these
equators and potentially forbidden fifth cuts:

| Source v | Opposite w | Equator | Only artificial edge at w |
|---|---|---|---|
| 1 | 5 | {0,2,3,4} | 50 |
| 3 | 2 | {0,1,4,5} | 24 |

At least one source has a maximum-curvature equator choice along an
original edge. Indeed, if every maximum for source 1 were forbidden,
vertex 0 would be its unique maximum, so kappa_0>kappa_4. For source 3,
the forbidden vertex 4 then cannot be a maximum because 0 is in its
equator too. If source 1 has a tie with any allowed vertex, use that
allowed vertex directly. This argument uses only the two displayed
equator sets and includes ties.

All nearby vertex curvatures are below pi. At the source and slit selected
above, the source-choice theorem therefore gives a nonoverlapping net.
The four source edges are original because sources 1 and 3 have degree
four already; the fifth edge is original by the selection argument.
Both artificial diagonals remain hinges.

There are at most six original star-plus-one-edge candidates (three at
each source). Pass to a fixed-tree subsequence and take the limit. At
least one of those six original trees unfolds the original solid. As in
the first type, only maxima at the limiting equator need be tried, but
all tied possibilities should be retained.

## 3. Construct the required strict refinements

One must not assume that an arbitrary formal triangulation is realizable.
Here the required refinements can be constructed directly.

For a convex planar quadrilateral with cyclic vertices X,U,Y,V and desired
diagonal XY, move X a small positive distance in the face's outward-normal
direction, leaving U,Y,V fixed. In the resulting four-point tetrahedron,
the two outward hull triangles are XUY and XYV. To check the choice of
diagonal, the old quadrilateral's diagonals cross internally: its affine
dependence has positive coefficients on X,Y and negative coefficients
on U,V. After lifting only X, that dependence determines exactly the
two supporting triangles incident to XY. Equivalently, project the new
triangles onto the old quadrilateral and check the fourth point lies
strictly below each outward plane. Thus the old facet is replaced by
the desired two triangles, with a strictly bent hinge XY.

For the minus-edge type, lift C out of the plane A-C-B-D to select CD.
For the prism type, lift 0 out of quadrilateral 0-3-5-2, and lift 4 out
of quadrilateral 1-2-5-4. Vertex 0 does not belong to the second
quadrilateral, and vertex 4 does not belong to the first. The two required
four-point signs can therefore be made independently and simultaneously.

Every other original face is a strictly supporting triangle. Its area,
and its strict separation from all nonincident vertices, persist under
sufficiently small movements. The new triangles are also strictly separated
from vertices outside their old quadrilateral by the original facet support
margin. The eight triangles therefore form a strict convex octahedron
with the prescribed graph for all sufficiently small positive lifts.
All incident face-angle sums vary continuously and approach the sums on
the original polygonal facets, so the strict curvature bound also persists.

## 4. Why an original-edge net survives the limit

Each selected cut tree uses five original edges. There are finitely many
such trees, so one occurs along a subsequence tending to the original
solid. Fix that tree. The uncut dual graph of the eight-triangle surface
is a tree, including each artificial diagonal as a hinge.

Fix a triangular root in the plane and develop each remaining triangle
across its unique hinge path. Edge lengths and nondegenerate triangle
altitudes converge, so these developed coordinates converge. Triangles
forming a limiting quadrilateral become coplanar on opposite sides of
their common uncut diagonal, and merge into the original quadrilateral.
The retained original hinges connect all original faces into one piece.

If two different limiting original faces had positive-area overlap,
their intersection would contain a point strictly inside one constituent
triangle of each, away from the finitely many artificial diagonal lines.
A small disk around that point would stay inside both triangles for
all sufficiently nearby refinements, contradicting their nonoverlap.
Boundary contact does not invalidate this argument. Thus the limiting
original faces have disjoint interiors.

## Scope of the computational checks

The checker `source_choice.py` tests the broader octahedron theorem on
explicit domains, without imposing H. `low_curvature_types.py` checks the
two original polygonal types, their strict curvature bounds, and the
diagonal-avoiding candidate sets. Its conclusion is existence among those
trees, not automatic success of the input certificate's particular tree.
Independent polygonal all-pair certificates check the displayed examples.
These programs are not a formal verification of the limiting proof.
