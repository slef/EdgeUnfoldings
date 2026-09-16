# A short guide to the Lean proof

The target theorem is still unfinished. The public vocabulary is only
[55 lines](SixVertexUnfolding/Definitions.lean), and the target is in
[Statement.lean](Statement.lean). Neither statement nor definition layer has been enlarged to accommodate the
proof machinery. The target proof invokes the current two-family reduction. You do not need to read the geometric helper modules to read
the statement.

`ConvexPolyhedron` is the convex hull of finitely many genuine extreme points
in three-dimensional Euclidean space, with nonempty interior. A face is a whole
two-dimensional supporting-plane intersection. An `EdgeUnfolding` gives one
rigid placement of each whole face in the plane, a tree of original-edge hinges,
agreement on every retained hinge, and disjoint planar face interiors. All of
these are requirements proved by a construction.

## The main proof, from top to bottom

| Read | What it establishes |
| --- | --- |
| [Bipyramid.lean](SixVertexUnfolding/Bipyramid.lean) | Every polyhedron with at most five vertices has the required unfolding. Complete. |
| [Pyramid.lean](SixVertexUnfolding/Pyramid.lean) | Every convex pyramid has one, with its base kept whole. Complete, including the six-vertex pentagonal-base case. |
| [Reduction.lean](SixVertexUnfolding/Reduction.lean) | The remaining inputs have exactly six vertices and only triangular or quadrilateral facets. Complete. |
| [SixVertexGraphs.lean](SixVertexUnfolding/Geometry/SixVertexGraphs.lean) and [SixVertexFacets.lean](SixVertexUnfolding/Geometry/SixVertexFacets.lean) | If no vertex is adjacent to every other vertex, the graph and whole facets have one of four explicit forms. Complete under this hypothesis. |
| [OctahedronComplete.lean](SixVertexUnfolding/OctahedronComplete.lean) | Every convex octahedron has the required original-edge unfolding. All angle cases, face comparisons, and hinge obligations are complete. |
| [MinusEdge.lean](SixVertexUnfolding/MinusEdge.lean) | The octahedron-minus-edge case, with its sole quadrilateral kept as one rigid original facet. Complete. |
| [PrismDiagonalSelection.lean](SixVertexUnfolding/PrismDiagonalSelection.lean) | Prism-with-diagonal when both degree-four endpoints are sharper than their opposite poles. Complete for this region. |
| [PrismComplete.lean](SixVertexUnfolding/PrismComplete.lean) | Every ordinary triangular prism. Complete, without parallelism assumptions, using the general dome theorem. |
| [SixVertexRemaining.lean](SixVertexUnfolding/SixVertexRemaining.lean) | The main target is reduced to universal-vertex solids and the prism with a diagonal. |

## The geometric core

The common development has four fan triangles `W0, …, W3` and four attached
petals `V0, …, V3`. All positions and angles come from the original solid.
The selected source is at least as curved as its opposite pole; the selected
equator slit has maximum curvature among the four equator vertices.

All **28 unordered triangle pairs** are now separated for the selected source
and slit. This includes both opposite-petal pairs and the four remote
fan–petal pairs. The resulting octahedron theorem has no remaining geometric
comparison premises.

[OctahedralFiniteContact.lean](SixVertexUnfolding/Geometry/OctahedralFiniteContact.lean)
proves both remote closed-cut exclusions, including endpoints and both source
curvature branches. Each proof has four stages: contact forces a reflex corner;
a ray reaches the copied cut edge; the neighboring apex lies in a finite
contact triangle; metric projection and determinant sine identities contradict
the selected curvature gates. The strict spatial link makes the curvature
budget strict. Selection also supplies the slit threshold, including ties.

The opposite-petal arguments split into Cases A, B, and the small-fan pocket.
Cases A and B are proved for the actual development, with their angle bounds.
The proof of Case B now reuses the common base-cone containment lemma.

## The completed pocket argument

[OctahedralPocketDiagonal.lean](SixVertexUnfolding/Geometry/OctahedralPocketDiagonal.lean)
constructs a quadrilateral from hypothetical overlap and proves that one
of its diagonals separates the other corners. Its two triangles define a
compact region with the exact four-side frontier and connected interior.

[OctahedralPocketFan.lean](SixVertexUnfolding/Geometry/OctahedralPocketFan.lean)
constructs the pole-sector seed and proves containment of the omitted fan.
[OctahedralPocketPatch.lean](SixVertexUnfolding/Geometry/OctahedralPocketPatch.lean)
constructs the petal seed and proves containment of the whole omitted patch.
Both orientations are covered, with no unproved seed assumptions.

The contained fan fixes the clockwise orientation. The four corner angles
sum to 2π, including reflex corners. Directions of rays into the two petals
give complementary-corner lower bounds. Together with the exact patch,
junction, slit, and pole identities, these contradict the proved curvature
budget. The final argument is
[OctahedralPocketContradiction.lean](SixVertexUnfolding/Geometry/OctahedralPocketContradiction.lean).
It avoids introducing a separate six-sided polygon after patch removal.
[POCKET_NEXT.md](POCKET_NEXT.md) records the completed proof map.

## The completed dome argument

[DomeComplete.lean](SixVertexUnfolding/Geometry/DomeComplete.lean) proves that
every convex polyhedron with a facet adjacent to all the others unfolds from
that facet. For parallel base hinges, exterior halfplanes separate the petals.
Otherwise the extended hinges meet at a virtual corner. Three independent
supporting normals construct the auxiliary apex, and supporting inequalities
contain both whole facets in separated corner cones. Rigidity, hinge agreement,
and outwardness are proved on the extended planes. This completes all ten
ordinary-prism face comparisons. [DOMES_NEXT.md](DOMES_NEXT.md) gives the map.

The remaining tasks are the six-vertex universal-vertex case and the
prism-with-diagonal case outside its proved curvature region. The flat-diagonal consistency and whole-face reassembly are
proved and applied to the minus-edge graph. The remaining prism cut choices
and geometric comparisons must still retain every original facet.

[SurfacePaths.lean](SixVertexUnfolding/Geometry/SurfacePaths.lean) defines
continuous paths on the actual boundary, with Mathlib total variation as arc
length. Straight paths within a face are shortest among all such paths.
[SixVertexStarCuts.lean](SixVertexUnfolding/Geometry/SixVertexStarCuts.lean)
proves that the five cuts at a universal vertex form a spanning tree of
shortest original edges and meet only at their source. Nonoverlap after these
cuts remains to be proved; it is not hidden in the path definition.

[ShortestSurfacePaths.lean](SixVertexUnfolding/Geometry/ShortestSurfacePaths.lean)
proves that any two boundary points have a finite shortest route, minimizing
among all continuous surface paths. Every portion of a shortest route is
shortest, so it cannot leave a face between two visits. The finitely many
face entry and exit times give a subdivision into straight face portions.
For distinct endpoints the route can be parametrized at constant arc speed
without self-intersections. [SHORTEST_PATHS.md](SHORTEST_PATHS.md) maps these
checked results. The cut-locus tree and star nonoverlap remain open.

[LOCAL_GEODESICS.md](LOCAL_GEODESICS.md) maps the flat metric charts now
constructed at every nonvertex boundary point. The affine shortest-path
formula and local nonbranching are proved. Vertex avoidance and global
nonbranching are also proved for all four canonical six-vertex graph models;
the universal-vertex family still needs vertex avoidance.

[CUT_LOCUS_FOUNDATIONS.md](CUT_LOCUS_FOUNDATIONS.md) maps the bounded
developments, actual local distance minima, and exact Voronoi description
both inside faces and across original edges. For canonical models, the
targets with three or more routes form a finite set on the whole surface.
Outside those targets and original vertices, every cut point has an actual
surface interval through it, preserving intrinsic distance and covering
all nearby multiple-route points. Adding original vertices other than the
source gives a compact cut set with contractible complement. It is now
proved to be exactly a finite union of closed segments, subdivided into an
embedded finite graph whose open edges are disjoint.
[ConnectedCutGraph](SixVertexUnfolding/Geometry/ConnectedCutGraph.lean) now proves
that graph connected. Every nonsource point has a unique terminal cut endpoint;
this gives a continuous retraction from the punctured boundary onto the cut
set. [CutSetContractible](SixVertexUnfolding/Geometry/CutSetContractible.lean)
proves the cut set itself contractible, and
[CutSetVertexLimits](SixVertexUnfolding/Geometry/CutSetVertexLimits.lean)
identifies it exactly with the closure of multiple-route targets.
[CutGraphAcyclic](SixVertexUnfolding/Geometry/CutGraphAcyclic.lean) proves
acyclicity by lifting an edge's circle map to a real potential.
[CutTreeLeaves](SixVertexUnfolding/Geometry/CutTreeLeaves.lean) proves that
all leaves are original vertices, using local regular arcs and finite
Voronoi diagrams.
[CutTreeRadialPartition](SixVertexUnfolding/Geometry/CutTreeRadialPartition.lean)
constructs two continuous route strips along each open edge. Their interiors
are disjoint, and they cover the surface together with the source, cut set,
and finitely many tree-vertex rays. Each route family extends continuously
to the edge endpoints.
[CutStripTriangleTopology](SixVertexUnfolding/Geometry/CutStripTriangleTopology.lean)
identifies each closed strip with a nondegenerate planar triangle by a
homeomorphism. The metric model has the correct base length and radial
distances, and the two model triangles meet exactly on their base.
[CutEdgeTriangleDevelopments](SixVertexUnfolding/Geometry/CutEdgeTriangleDevelopments.lean)
constructs both actual triangle developments for every cut-tree edge.
Their maps preserve distances on convex portions of original faces and on
convex flat-chart patches, including across original hinges.
[RadialStripRigidCharts](SixVertexUnfolding/Geometry/RadialStripRigidCharts.lean)
proves that each local flat disk develops by one rigid planar motion.
[RadialStripInterior](SixVertexUnfolding/Geometry/RadialStripInterior.lean)
identifies the open strip exactly with the triangle interior.
[CutTreeTrianglePairs](SixVertexUnfolding/Geometry/CutTreeTrianglePairs.lean)
now joins two successive actual strips sharing an endpoint route: one
rigid motion aligns that whole route, the triangles meet exactly along it,
and their maps paste into a homeomorphism of the two-strip union.
The actual nonvertex junction fans and opposite-edge triangle agreement
are now constructed. The original cone inequalities and total/simple-path
source-angle budgets are proved. Wedge frame compatibility, first-kite
containment, finite region iteration, and terminal exclusion are checked,
with actual applications at one and two junctions. See
[WEDGE_CHAINS.md](WEDGE_CHAINS.md). The global cut surface, internal original-vertex
junctions, full path application with surface correspondence, and whole-face
transfer remain open; [GLOBAL_ASSEMBLY.md](GLOBAL_ASSEMBLY.md) states the next
construction without assuming those conclusions.

[SIX_VERTEX_STATUS.md](SIX_VERTEX_STATUS.md) gives the detailed map.
[Audit.lean](Audit.lean) checks every proved-library declaration and rejects any
extra axiom or hidden `sorry`. The one unfinished target in `Statement.lean` is
checked separately and is not imported by the proved library.
