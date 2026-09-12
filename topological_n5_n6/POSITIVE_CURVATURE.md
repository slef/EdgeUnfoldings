# A partial extension for five vertices with strictly positive curvature

13 September 2026. Written deduction using established intrinsic realization
and star-unfolding theorems. Not formalized in Lean. No novelty claim.

## Proposition

Let P be an embedded polyhedral sphere with a 3-connected planar original
edge graph, exactly five vertices, nondegenerate planar faces, and strictly
positive angle defect at each vertex. Then P has an original-edge unfolding
with disjoint face interiors. In fact, cutting the star of any degree-four
vertex works. P need not be geometrically convex in its given embedding.

## Proof

**1. A universal vertex exists.** Every vertex of the graph has degree at
least three. If all five had degree three, the degree sum would be fifteen,
which is impossible. Some vertex s therefore has degree four.

**2. Its four edges are unique shortest surface paths.** For each other
vertex v, the original straight segment sv is on the surface. Its length
equals the ambient Euclidean distance |s-v|. Every rectifiable surface path
from s to v has at least that length. Equality forces the image of the path
to be the straight segment sv, up to reparametrization. Since the polyhedral
surface is embedded, it cannot contain two distinct such paths with the
same spatial image. Thus all four original edges are unique intrinsic
shortest paths. They meet only at s, as required by the original cell complex.

**3. Realize the metric convexly, retaining the marked paths.** The intrinsic
surface metric is locally Euclidean away from its five vertices and has
positive angle defect at each vertex. Alexandrov's realization theorem
gives an isometric convex polyhedral surface, possibly a doubly covered
convex polygon. See [Petrunin and Yashinski, Theorem 1.16](https://anton-petrunin.github.io/alexandrov/alexandrov-old.pdf).
The five positive-curvature points are exactly the five vertices of that
realization. The original source edges become marked shortest paths; no
assumption that they become convex-hull edges is made.

**4. Exclude the degenerate realization.** If this realization were a doubly
covered convex polygon, its five vertices would be genuine corners because
all five curvatures are strictly positive. The image of s is one corner.
Choose a nonadjacent corner v. The straight chord sv lies in the polygon's
interior except at its endpoints. Its copy on each of the two sheets is a
shortest path, giving two distinct equal-length intrinsic shortest paths.
This contradicts Step 2. The convex realization is therefore three-dimensional.

**5. Apply the star theorem and transfer the development.** Cut the four
marked shortest paths on that convex surface. The star-unfolding theorem
gives a nonoverlapping planar development, including when the source is a
vertex; see Definition 1 and Theorem 4 of
[Kiazyk and Lubiw (2015)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SOCG.2015.390).
Pull back this cut and development by the intrinsic isometry. The cuts are
exactly the original edges sv. Each original face remains whole and develops
rigidly: on its flat connected interior the planar development is a local
Euclidean isometry, hence one rigid motion, with agreement on uncut hinges.
The pulled-back map has the same image and therefore the same nonoverlap.
This proves the proposition.

## A concrete nonconvex family it includes

Choose a nondegenerate triangle ABC in a plane. Let O lie strictly inside it
and let n be a unit normal. For h>k>0 set P=O+h*n and Q=O+k*n. Use the six
triangular faces of the two caps over ABC, one with apex P and one with
apex Q, joined along the three equator edges. This is an embedded nonconvex
sphere: the smaller tetrahedral cap lies strictly inside the larger one,
apart from their common triangular rim.

Reflect Q to Q'=O-k*n. The six original triangles keep exactly their side
lengths. The resulting bipyramid is strictly convex because the pole segment
crosses the interior of ABC and the two apices lie on opposite sides. Its
edge-star nets transfer face by face to the original dented realization.
In particular the original nonconvex sphere has strictly positive intrinsic
curvature at every vertex, inherited from that convex realization.

The exact example with A=(-1,-1,0), B=(1,-1,0), C=(0,1,0), P=(0,0,3),
Q=(0,0,1) is checked in `exact_topological_audit.py`. Its pole segment misses
the equator plane, so it also illustrates why the current ambient Radon
argument cannot simply be reused unchanged.

## Boundaries of this repair

The proof requires strictly positive curvature. With negative curvature,
Alexandrov's convex realization is unavailable and a leaf of the cut tree
can have more than a full turn of incident face angles. The exact two-saddle
bipyramid shows that every universal-vertex star may fail.

The zero-curvature boundary has not been added by an unproved continuity
argument. It needs either a treatment of marked flat vertices and possible
degenerate realizations, or a justified approximation preserving the needed
original-edge cuts. Consequently this result does not settle Conjecture 9.

For a concave quadrangular pyramid the reflex base corner necessarily has
negative curvature, so this proposition does not address that missing case.
For arbitrary six-vertex graphs, convex realization alone does not turn the
original edges into convex-hull edges. One cannot use the convex six-vertex
edge-unfolding theorem and assume that its cuts pull back to original edges.
