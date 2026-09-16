# A small statement layer for the six-vertex theorem

The recommendation is to use an actual convex solid in Euclidean three-space as
the starting point. A planar graph records incidence, but not the lengths and
angles needed to talk about unfolding a particular polyhedron. Starting with a
convex hull gives both geometry and incidence without making a theory of
polyhedral surfaces, planar embeddings, or three-connectivity part of the
statement.

The initial draft contained the entire proposed definition layer and target
theorem in 61 lines, including comments and blank lines. During the first proof
pass, the definitions were moved unchanged to
[Definitions.lean](SixVertexUnfolding/Definitions.lean), and
[Statement.lean](Statement.lean) retained the target theorem. See
[README.md](README.md) for the current formalization status. The following
records the original modeling proposal.

Read the definitions as follows:

- `Space` and `Plane` are Euclidean three-space and two-space. Using
  `EuclideanSpace` makes `dist` the usual Euclidean distance.
- `ConvexPolyhedron` supplies a finite set of vertices. Its convex hull has
  nonempty three-dimensional interior, and the listed vertices are exactly its
  extreme points. Thus the theorem counts actual vertices and concerns bounded
  solids, including ones with polygonal faces of more than three sides.
- `IsFace` means a two-dimensional intersection of the whole solid with a
  supporting plane. The equality in the definition requires the whole face.
  `Face` ranges over all such sets, so no face can be omitted or listed twice.
- `ShareEdge` means that two faces intersect in dimension one. For distinct
  facets of a convex polyhedron, this is exactly an original edge.
- `EdgeUnfolding` chooses planar placements and a tree on all faces. Its tree
  edges are the **uncut hinges**. Every hinge must be an original shared edge,
  distances within each face must be preserved, placements must agree at every
  point of every hinge, and distinct placed faces must have disjoint interiors.

The map `place F` is written as a function on three-space just to keep the syntax
simple. Its values outside `F` are never used or constrained. Rigidity is required
for every pair of points of the whole face, so a quadrilateral cannot bend along
a diagonal. Matching coordinates at a cut edge by coincidence does not glue that
edge; the tree specifies the retained identifications.

The convention here matches the existing repository: boundary contact is
permitted, but face interiors cannot overlap. The interiors in the code are
taken **in the target plane**. Taking ordinary interiors of faces in three-space
would make the nonoverlap condition vacuous. This draft does not demand a strictly
simple boundary or a collision-free continuous motion from the solid to the net.

For a convex polyhedron, retaining a spanning tree of face adjacencies is the
dual description of cutting a spanning tree of original edges. Gluing separate
copies of the polygonal faces only along those hinges gives an abstract disk.
Boundary contacts in its planar image are allowed by the chosen convention.
These facts explain the intended meaning; their Lean proofs are not supplied.

Subsequent proof work has established the finite polygonal facets, their
coverage of the boundary, the segment characterization of shared edges, exactly
two facets at each edge, and the absence of crossings between different edges.
The original vertex-edge graph has minimum degree three and remains connected
after deleting any two vertices. The dual graph is connected, and rigid
development along any chosen hinge tree is proved. The equivalence with cutting
an original-edge spanning tree to obtain an
abstract disk remains to be formalized. These are general bridge lemmas, not
additional hypotheses imposed on the six-vertex theorem. See the current
[progress report](README.md) for the precise proved results and remaining work.
The entire four-vertex unfolding case is now proved against these unchanged
definitions in [Tetrahedron.lean](SixVertexUnfolding/Tetrahedron.lean); the main
statement invokes that proof. The full pyramid construction is also proved in
[Pyramid.lean](SixVertexUnfolding/Pyramid.lean), including the five-vertex case
with a quadrilateral base and the six-vertex case with a pentagonal base. Its
small `Pyramid` structure belongs only to the proof layer; the public definitions
remain unchanged. [Reduction.lean](SixVertexUnfolding/Reduction.lean) now leaves
only six vertices with triangular or quadrilateral facets as an unfinished family.

The bipyramid proof is now complete. It identifies all six original facets,
constructs a rigid development about an equator vertex, and separates all 15 face
pairs. An exact weighted squared-distance identity supplies the missing vertex
comparisons; a boundary argument settles the remaining base/petal pairs.
[Bipyramid.lean](SixVertexUnfolding/Bipyramid.lean) therefore proves every convex
polyhedron with at most five vertices against the unchanged public definitions.
The general six-vertex theorem remains unfinished. The public definition layer
is still the same 55 lines.

Mathlib already supplies
[convex hulls](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Hull.html),
[extreme points](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Extreme.html),
and [trees](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Acyclic.html).
There is also an external
[polyhedral geometry project](https://github.com/uw-math-ai/lean-polyhedral-geometry),
whose stated scope includes the equivalence of halfspace and convex-hull
representations. It has not been adopted or audited here. No additional package
is needed for this statement; any later package could supply proof lemmas while
the theorem continues to use these explicit definitions.

Validation: Lean 4.29.1 accepted this file against Mathlib commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`, using the existing local installation
read-only. The only diagnostic was the expected warning about the theorem's
`sorry`. This validates the Lean syntax and types, not the theorem or the
mathematical equivalences discussed above. No existing proof files were edited.
