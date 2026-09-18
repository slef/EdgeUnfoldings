# Lean formalization of the six-vertex edge-unfolding theorem

The public definitions and target proposition remain unchanged. The target
proof now closes the universal-vertex branch using the completed star construction. **The main
six-vertex theorem is not yet proved in Lean.** The complete theorem for **at
most five vertices**, the theorem for **every convex pyramid**, and the
**octahedron**, **octahedron-minus-edge**, and **ordinary triangular-prism**
cases are proved. Every convex dome is also proved edge-unfoldable.
Every polyhedron with at most six vertices and a universal vertex is now
proved edge-unfoldable as well. The single remaining `sorry` in
[Statement.lean](Statement.lean) concerns the prism-with-diagonal branch. None of the proved modules
imports that unfinished theorem.

The mathematical starting point is the revised manuscript in
`n6/TIDY_PROOF.md`, with `n6/TIDY_CORE.md`, `n6/PAIRED_POLE_RULE.md`, and
`n6/PRISM_CAP_RULE.md`. The repository checkpoint when this first formalization
pass was checked was `5b21be4896f9e178626f1ca4fdcdc7e7458b93dc`.
All changes for this work are confined to `lean_statement/`.

[INTEGRATION.md](INTEGRATION.md) records the dedicated Lean worktree,
checkpoint policy, build instructions, and planned links from the interactive
paper. [STAR_NEXT.md](STAR_NEXT.md) is the current star-theorem checkpoint;
read it before older continuation notes.

Read the [interactive full-proof overview](star-paper/dist/proof.html) for the
case map, mathematical exposition and expandable checked Lean statements.
It links to the detailed [star-unfolding chapter](star-paper/dist/index.html)
and explicitly marks the remaining prism-with-diagonal steps.

## Reading order

[PROOF_GUIDE.md](PROOF_GUIDE.md) is a short overview of the proof and its exact
unfinished boundaries.
[CUT_LOCUS_FOUNDATIONS.md](CUT_LOCUS_FOUNDATIONS.md) maps this continuation's
new shortest-route geometry and topology, with the remaining gaps stated explicitly.
[WEDGE_STEP.md](WEDGE_STEP.md) isolates the current planar wedge argument,
its checked rotation-and-root-movement step, and the remaining connection
to the actual cut surface.
[JUNCTION_ORDER.md](JUNCTION_ORDER.md) records the checked angular order of
actual shortest-route tails and the cut rays between consecutive source copies.
[CONE_BUDGET.md](CONE_BUDGET.md) maps the proved cone and simple-path angle bounds.
[WEDGE_CHAINS.md](WEDGE_CHAINS.md) maps the checked initial, intermediate,
terminal, and finite-chain wedge results.
[GLOBAL_ASSEMBLY.md](GLOBAL_ASSEMBLY.md) describes the checked cofacial star
construction in the canonical and universal-source scopes, with arbitrary-source limitations.

1. [Definitions.lean](SixVertexUnfolding/Definitions.lean) contains the entire
   public mathematical vocabulary: the original definitions, moved verbatim.
2. [Statement.lean](Statement.lean) gives the unchanged target theorem.
3. [SixVertexUnfolding.lean](SixVertexUnfolding.lean) lists the proved modules.
   Each module has a short introduction and small, named lemmas.
4. [Tetrahedron.lean](SixVertexUnfolding/Tetrahedron.lean) is the complete
   four-vertex proof, with the same public definition of an edge unfolding.
5. [Pyramid.lean](SixVertexUnfolding/Pyramid.lean) is the complete pyramid proof,
   including the five-vertex quadrilateral-base and six-vertex pentagonal-base cases.
6. [Bipyramid.lean](SixVertexUnfolding/Bipyramid.lean) completes the triangular
   bipyramid and then every convex polyhedron with at most five vertices.
7. [Reduction.lean](SixVertexUnfolding/Reduction.lean) leaves only six vertices
   with triangular or quadrilateral facets.
8. [SIX_VERTEX_STATUS.md](SIX_VERTEX_STATUS.md) gives the completed six-vertex
   graph and facet classification, the quadrilateral lemmas, and remaining work.
9. [BIPYRAMID_STATUS.md](BIPYRAMID_STATUS.md) gives the complete five-vertex proof
   map, including the weighted distance identity and the boundary argument.

The complete pyramid theorem is
[`every_convex_pyramid_has_edge_unfolding`](SixVertexUnfolding/Pyramid.lean).
The proof-only `Pyramid` structure says exactly that all original vertices except
one apex lie in a single original base facet. No vertex-count bound is needed for
this result. Lean derives every triangular side face and its original base hinge,
places the base rigidly, and unfolds each side outward. The base remains a whole
polygon. Supporting-plane inequalities keep it opposite every petal, while
Cauchy–Schwarz gives strict apex-copy distance comparisons at every missing base
vertex. Perpendicular bisectors between the copies separate all pairs of petals.
The retained hinges form a tree of original edges. No shortest-path star theorem
is assumed. The earlier complete tetrahedron proof remains available separately.

The original vertex-edge graph is now constructed from the geometric definition.
Lean proves that it has minimum degree three and remains connected after deleting
any two vertices:
[`edgeGraph_three_connected`](SixVertexUnfolding/Geometry/ThreeConnectivity.lean).
Every original edge has exactly two incident facets, and different edges meet
only at common endpoints. The four- and five-vertex universal-vertex reductions
now apply directly to the polyhedron, without assumed graph properties.
[FiveVertexNonedge](SixVertexUnfolding/Geometry/FiveVertexNonedge.lean) uses
Mathlib's Radon theorem to prove that any five original vertices contain a
nonadjacent pair. Together with minimum degree three,
[FiveVertexGraphs](SixVertexUnfolding/Geometry/FiveVertexGraphs.lean) proves that
a five-vertex graph is complete except for one or two disjoint missing edges.
For triangular facets, [FiveVertexTriangularGraph](SixVertexUnfolding/Geometry/FiveVertexTriangularGraph.lean)
now proves that there is exactly one missing edge. Its endpoints are the two
poles; the other three vertices are the equator. The original facets are exactly
the six pole-and-equator triangles, proved using original edges and their two
incident facets. This classification does not assume a planar graph embedding.

[BipyramidDevelopment](SixVertexUnfolding/Geometry/BipyramidDevelopment.lean)
constructs the star development about any equator vertex. Its five retained
hinges form a tree and keep exactly the original edges away from that source.
[BipyramidCuts](SixVertexUnfolding/Geometry/BipyramidCuts.lean) proves that the four
cut source edges form a spanning tree of the original vertex-edge graph.
**All 15 distinct face pairs are now proved nonoverlapping.**

The new argument uses the strict crossing of the pole segment through the equator
triangle. Positive barycentric weights give an exact squared-distance identity;
[RadonMetric](SixVertexUnfolding/Geometry/RadonMetric.lean) uses it to show that the
missing pole-to-source-copy distances increase after development. Voronoi
comparisons then separate every pair of petals. Finally,
[BoundaryBarrier](SixVertexUnfolding/Geometry/BoundaryBarrier.lean) proves that a
convex petal cannot enter a base whose three boundary edges are covered by
already-separated neighboring faces. The opposite pole supplies a point outside
the base. [BipyramidNonoverlap](SixVertexUnfolding/Geometry/BipyramidNonoverlap.lean)
assembles every comparison into the unchanged public unfolding predicate.
This proof needs neither the general shortest-path star theorem nor vertex
curvature positivity.

The previously established bipyramid curvature results remain available:
actual corner angles, total defect 4π, positive pole defects, every defect below
2π, and positivity of a maximum equator defect. Positivity of all equator defects
is still unfinished, but is no longer needed for the completed five-vertex proof.

For arbitrary vertex count,
[`exists_rigid_development`](SixVertexUnfolding/Geometry/DualConnectivity.lean)
proves that every public polyhedron has a spanning tree of original face
hinges and simultaneous rigid planar placements agreeing along those hinges.
These placements may overlap. Choosing a development without overlaps for the
remaining prism-with-diagonal family is the central unfinished task.

For the eventual case constructions,
[`hasEdgeUnfolding_of_vertex_certificate`](SixVertexUnfolding/Geometry/VertexCertificate.lean)
reduces rigidity, hinge agreement, and separation to checks on original vertices.
Its conclusion is the actual public `HasEdgeUnfolding` predicate.
For rigid affine placements, [PlacedFaces](SixVertexUnfolding/Geometry/PlacedFaces.lean)
also proves that each placed facet has nonempty planar interior and that the
vertex-separator condition is equivalent to disjoint face interiors.

## What is proved

| Module | Kernel-checked results | Boundary of the result |
| --- | --- | --- |
| [BipyramidFacets](SixVertexUnfolding/Geometry/BipyramidFacets.lean), [BipyramidFaceIndex](SixVertexUnfolding/Geometry/BipyramidFaceIndex.lean), [BipyramidDual](SixVertexUnfolding/Geometry/BipyramidDual.lean) | A five-vertex solid with triangular facets has exactly two poles, three equator vertices, six original triangular facets, and the nine stated original facet adjacencies. | Complete classification of the remaining five-vertex surface; no graph embedding assumption. |
| [TrianglePetal](SixVertexUnfolding/Geometry/TrianglePetal.lean), [PetalPlacement](SixVertexUnfolding/Geometry/PetalPlacement.lean), [BipyramidCap](SixVertexUnfolding/Geometry/BipyramidCap.lean), [BipyramidTree](SixVertexUnfolding/Geometry/BipyramidTree.lean), [BipyramidDevelopment](SixVertexUnfolding/Geometry/BipyramidDevelopment.lean) | Certified outward petals give nonoverlapping cap developments. Joining their bases produces the concrete six-face star development with rigid faces, a tree of original hinges, and seven proved face-pair separations. The eight remaining comparisons imply the public unfolding predicate. | This is the construction layer; the eight comparisons are discharged in BipyramidNonoverlap. The pyramid proof also reuses the general triangular-petal lemma. |
| [BipyramidRadon](SixVertexUnfolding/Geometry/BipyramidRadon.lean) | The pole segment intersects the equator triangle strictly between the poles and away from all equator edges. | A spatial description derived from Radon and the unique nonedge, without extra geometric assumptions. |
| [Curvature/Bipyramid](SixVertexUnfolding/Curvature/Bipyramid.lean), [ThreeRays](SixVertexUnfolding/Curvature/ThreeRays.lean) | Actual bipyramid corner angles have total defect 4π. Both pole defects are positive; equator corners lie strictly between zero and π. Every vertex defect is below 2π, and a maximum-defect equator source has positive defect. | Positivity at every equator vertex and the required nonoverlap consequences remain open. This does not supply general six-vertex curvature theory. |
| [Pyramid](SixVertexUnfolding/Pyramid.lean), [PyramidFaces](SixVertexUnfolding/Geometry/PyramidFaces.lean), [PyramidPetal](SixVertexUnfolding/Geometry/PyramidPetal.lean), [PyramidCertificate](SixVertexUnfolding/Geometry/PyramidCertificate.lean), [Reduction](SixVertexUnfolding/Reduction.lean) | Every convex pyramid has an original-edge unfolding with its polygonal base kept whole. This proves the quadrilateral-base case at five vertices and pentagonal-base case at six, and reduces the main theorem to two explicit remaining families. | Complete for pyramids of any size. All five-vertex cases are now complete; other six-vertex families remain. The pyramid description is confined to the proof modules. |
| [FacetCoordinates](SixVertexUnfolding/Geometry/FacetCoordinates.lean), [FacetHingeSides](SixVertexUnfolding/Geometry/FacetHingeSides.lean) | Three noncollinear facet points span its plane. A supporting neighboring facet puts all base points on the same closed hinge side, also after affine placement. | Used to prove base-petal separation and all missing-vertex comparisons in the pyramid construction. |
| [FiveVertexNonedge](SixVertexUnfolding/Geometry/FiveVertexNonedge.lean), [EdgeHullSeparation](SixVertexUnfolding/Geometry/EdgeHullSeparation.lean), [FiveVertexGraphs](SixVertexUnfolding/Geometry/FiveVertexGraphs.lean) | An original edge misses the convex hull of its other original vertices. Radon supplies an intersecting segment and complementary hull, excluding a complete graph on any five original vertices. A five-vertex polyhedron has exactly one or two disjoint missing edges. | The triangular-facet refinement and original face lists are now proved in the bipyramid modules above. |
| [Tetrahedron](SixVertexUnfolding/Tetrahedron.lean), [TetrahedronFaces](SixVertexUnfolding/Geometry/TetrahedronFaces.lean), [TetrahedronHinges](SixVertexUnfolding/Geometry/TetrahedronHinges.lean), [TetrahedronPetal](SixVertexUnfolding/Geometry/TetrahedronPetal.lean), [TetrahedronCertificate](SixVertexUnfolding/Geometry/TetrahedronCertificate.lean) | Every public convex polyhedron with exactly four genuine vertices has an original-edge unfolding, with rigid whole faces, matching hinges, and disjoint face interiors. | A complete case, without extra geometric hypotheses or proof holes. |
| [HingeMetricComparison](SixVertexUnfolding/Geometry/HingeMetricComparison.lean), [TriangleStrictComparison](SixVertexUnfolding/Geometry/TriangleStrictComparison.lean), [OutwardTriangle](SixVertexUnfolding/Geometry/OutwardTriangle.lean), [VoronoiSeparation](SixVertexUnfolding/Geometry/VoronoiSeparation.lean) | Outward flattening increases the free-vertex distance, strictly for noncoplanar triangles. An aligned triangle can be reflected to the outward side. Nearest-source comparisons at original vertices separate entire faces. | Used in the complete tetrahedron and pyramid proofs. Their extension to the remaining configurations still needs work. |
| [Geometry/Polyhedron](SixVertexUnfolding/Geometry/Polyhedron.lean) | The body is compact and convex, its specified vertices are its extreme points, and it has at least four vertices. At most six therefore means four, five, or six. | Directly about the public `ConvexPolyhedron`. |
| [Geometry/Faces](SixVertexUnfolding/Geometry/Faces.lean), [FacetVertices](SixVertexUnfolding/Geometry/FacetVertices.lean) | Every face is nonempty, compact, convex, exposed, and the convex hull of its original vertices. There are finitely many faces. Each face contains at least three vertices and omits at least one vertex of the solid. | Direct consequences of the public definition. |
| [Geometry/BoundaryCoverage](SixVertexUnfolding/Geometry/BoundaryCoverage.lean) | The union of all facets is exactly the boundary. A finite maximal-contact argument enlarges supporting vertex or edge contacts to facets. | The supporting-plane and tilting arguments are proved in the imported helper modules. |
| [Geometry/Edges](SixVertexUnfolding/Geometry/Edges.lean), [Intersections](SixVertexUnfolding/Geometry/Intersections.lean), [EdgeIncidence](SixVertexUnfolding/Geometry/EdgeIncidence.lean), [EdgeIntersections](SixVertexUnfolding/Geometry/EdgeIntersections.lean) | Distinct facets meet in dimension at most one. Each shared edge is a whole segment with two original endpoints and exactly two incident facets. Different edges meet only at common endpoints. Three distinct original vertices cannot be collinear. | Cyclic facet boundary orders and their relation to a planar graph embedding remain unfinished. |
| [Geometry/FacetHalfspaces](SixVertexUnfolding/Geometry/FacetHalfspaces.lean), [VertexFacets](SixVertexUnfolding/Geometry/VertexFacets.lean) | Facet halfspaces recover the solid. At every original vertex their active normals span three-space, giving at least three incident facets. | The separate vertex-figure argument below proves the edge-degree bound. |
| [Geometry/ContactFacets](SixVertexUnfolding/Geometry/ContactFacets.lean), [EdgeGraph](SixVertexUnfolding/Geometry/EdgeGraph.lean), [VertexFigure](SixVertexUnfolding/Geometry/VertexFigure.lean), [VertexFigureEdges](SixVertexUnfolding/Geometry/VertexFigureEdges.lean) | Every one-dimensional supporting contact is a whole shared facet edge. A transverse vertex figure has at least three corners, each corresponding to a different original edge neighbor. Thus the original vertex-edge graph has minimum degree three. | All conclusions follow from the public geometric definition. |
| [Geometry/EdgeConnectivity](SixVertexUnfolding/Geometry/EdgeConnectivity.lean), [HalfspaceConnectivity](SixVertexUnfolding/Geometry/HalfspaceConnectivity.lean), [ThreeConnectivity](SixVertexUnfolding/Geometry/ThreeConnectivity.lean) | A nonmaximal vertex has an ascending original edge. Strict halfspaces induce connected graphs when nonempty. Removing any two vertices leaves the original edge graph connected. | Three-connectivity is proved in the literal vertex-deletion form; planarity remains unfinished. |
| [Geometry/SurfaceTopology](SixVertexUnfolding/Geometry/SurfaceTopology.lean), [DualConnectivity](SixVertexUnfolding/Geometry/DualConnectivity.lean) | The boundary is homeomorphic to a sphere and remains path connected after removing finitely many points. The facet dual graph is connected and has a spanning tree. | Turning the geometric edges on this sphere into the planar graph theory used by the classification remains unfinished. |
| [Geometry/FacePlacement](SixVertexUnfolding/Geometry/FacePlacement.lean), [HingePlacement](SixVertexUnfolding/Geometry/HingePlacement.lean), [TreeDevelopment](SixVertexUnfolding/Geometry/TreeDevelopment.lean) | Every facet admits rigid planar coordinates. Equal-length hinge segments can be aligned. Unique tree paths assemble simultaneous rigid placements agreeing along every hinge. | The construction does not yet enforce opposite sides at adjacent faces or nonoverlap. |
| [Geometry/VertexCertificate](SixVertexUnfolding/Geometry/VertexCertificate.lean), [PlacementRigidity](SixVertexUnfolding/Geometry/PlacementRigidity.lean), [Separation](SixVertexUnfolding/Geometry/Separation.lean) | Vertex distances establish whole-face rigidity; shared-vertex agreement establishes whole-hinge agreement; vertex halfplane separators establish disjoint face interiors. Together these prove the public unfolding predicate. | The required successful placements and separators must be supplied by the geometric case proofs. |
| [Geometry/PlacedFaces](SixVertexUnfolding/Geometry/PlacedFaces.lean) | Every rigidly placed facet spans the plane and has nonempty planar interior. For rigid affine placements, disjoint face interiors are equivalent to a separator checked on original vertices. | This validates the certificate interface; it does not yet supply the successful six-vertex certificates. |
| [Curvature/Selection](SixVertexUnfolding/Curvature/Selection.lean) | An equator maximum exists and meets the slit threshold and lower face budgets; the half-fan alternative and complementary-triple bound also hold. | Positivity, the total curvature, and source bounds are explicit real-number hypotheses. |
| [Curvature/PairedPoles](SixVertexUnfolding/Curvature/PairedPoles.lean) | Both fourth-petal remainder identities and both wider Case A bounds, including tied source curvatures. | The face-angle sums and strict spherical-link bounds are explicit hypotheses. |
| [Curvature/Obstructions](SixVertexUnfolding/Curvature/Obstructions.lean) | The strict finite-contact budget and the contradictions ruling out contact and small-fan pockets under criterion (P). | This scalar module supplies the final contradictions. Both finite-contact implications and both pocket contradictions are now proved for the actual development. |
| [Curvature/Prism](SixVertexUnfolding/Curvature/Prism.lean) | The cap identity, wider bounds, exhaustive cap alternatives, high-cap gates, and the two elementary angle alternatives. | The geometric correctness of each selected net and the sharp-fan switch remain open in Lean. |
| [SmallGraphs](SixVertexUnfolding/SmallGraphs.lean), [Geometry/SmallPolyhedra](SixVertexUnfolding/Geometry/SmallPolyhedra.lean) | All pairs of distinct vertices are adjacent when there are four vertices. Every polyhedron with at most five vertices has a universal vertex. With six vertices and no universal vertex, complement degrees are one or two. | The general star-unfolding theorem remains unfinished. The nonuniversal six-vertex classification is complete. The tetrahedron proof uses its own explicit construction. |

The scalar lemmas quantify over real numbers with the displayed hypotheses.
They do not assert that arbitrary angle or curvature assignments come from a
convex polyhedron. Their future use requires a geometric construction producing
those numbers and proving the hypotheses. The five-vertex unfolding case is now proved by the explicit bipyramid and pyramid constructions.

## Quantified progress

Continuation checkpoint, 16 September 2026 (Europe/Brussels):

| Indicator | Current assessment |
| --- | --- |
| Public definitions and target statement | 100%; unchanged 55-line definition layer. |
| Basic geometric and graph foundations | Many named results are checked; general planarity and cyclic facet boundaries remain unfinished. No reliable effort percentage is assigned. |
| Common geometric core | Complete for the selected eight-triangle development, including both small-fan pocket cases. |
| Completed cases | At most five vertices, all pyramids and domes, octahedra, octahedra minus one edge, and ordinary triangular prisms. |
| Five-vertex bipyramid | Complete classification, construction, original hinge tree, and all 15/15 face-pair separations. |
| Selected eight-triangle development | 28/28 pair separations (100%), with no remaining comparison premises. |
| Nonuniversal six-vertex graph families | 3/4 complete (75%): octahedron, minus-edge, and ordinary prism. Prism-with-diagonal has enlarged proved regions. |
| Ordinary prism flower | 10/10 whole-face pairs (100%) for arbitrary geometry. The general dome theorem is complete. |
| Remote finite-cut exclusions | 2/2 complete (100%) for every selected source/slit, including endpoints and curvature-threshold equalities. |
| General shortest-path milestone | 3/3 complete: existence among all continuous surface paths, finite straight face subdivision, and a simple constant-speed parametrization for distinct endpoints. This is a prerequisite, not star nonoverlap. |
| Local shortest-path geometry | Flat metric charts and local nonbranching are proved for every polyhedron. Vertex avoidance, finite route fibers, and global disjointness now hold for every polyhedron with at most six vertices and triangular/quadrilateral faces, without a canonical graph premise. |
| Extension to universal-vertex solids | The actual cut tree, complete radial triangle charts, and original-vertex leaves are proved. The full universal-source star embedding is now proved, including local metric, connectivity, and polygonal boundary. Its whole-face conversion gives the public edge unfolding. |
| Finite route structure | For at most six vertices and triangular/quadrilateral faces, intrinsic distance is locally the minimum over actual active sources, both in faces and across original edges. These sources count actual routes bijectively, and their Voronoi boundary is exactly the nearby multiple-route locus. |
| Face-interior cut-locus milestone | 4/4 checked: actual nearby competitors, finite local minimum, exact Voronoi description, and ordinary two-route points with finitely many junctions. This is a local prerequisite, not the global tree theorem. |
| Edge-interior cut-locus milestone | 4/4 checked: actual nearby competitors, finite local minimum, exact Voronoi description, and full two-route bisectors. Both incident original faces are covered. |
| Global junctions and regular arcs | Junctions are finite on the entire surface. Outside them and original vertices, every cut point has a checked surface interval preserving intrinsic length and covering nearby multiple-route points. |
| Finite cut-graph milestone | Exact finite segment decomposition and a finite embedded tree are proved for at most six vertices with triangular/quadrilateral faces, from any surface source. Under cofaciality, every original cut vertex is now proved a leaf. |
| Cut-set topology | The actual cut set is compact and contractible for at most six vertices with triangular/quadrilateral faces. The terminal-ray endpoint map is a continuous retraction of the punctured boundary onto it. Equality with the closure of the multiple-route locus remains checked in the canonical scope. |
| Cut-tree leaves and subdivision | Every leaf is an original nonsource vertex; an original source has at most five leaves. A refined tree marks all junctions and original vertices, so every open edge has exactly two shortest routes. |
| Tree properties | Connectedness and acyclicity are now proved for at most six vertices with triangular/quadrilateral faces, without a canonical graph premise. All junctions and original cut vertices are marked, and every open edge has exactly two shortest routes. |
| Route stability | For at most six vertices with triangular/quadrilateral faces, uniqueness persists and route counts cannot increase near any nonvertex target, including original edge interiors. The multiple-route locus is closed there. For every public polyhedron, it cannot accumulate at the source. |
| Radial surface partition | For at most six vertices with triangular/quadrilateral faces, every cut-tree edge has two continuous closed route families and actual triangle developments. Their regions cover the entire boundary, for any surface source. |
| Radial triangle geometry | Actual triangle developments, open strips, metric compatibility, flat junction fans, and coherent tree frames are checked without a canonical graph. Cofacial sources give complete CutTreeCharts. The global star embedding is checked both for canonical cofacial sources and for the six-vertex universal-source family. |
| Successive radial triangles | Actual strips sharing an endpoint route align outward. The broader cofacial chart construction now includes the actual flat fans and coherent frames. Global kite separation is now proved for six vertices with a universal source. |
| Original nonsource cone inequalities | All original vertices are covered for at most six vertices with triangular/quadrilateral faces; no canonical graph premise. Global source-angle budgets are now also proved for six vertices with a universal source, using actual face angles. |
| Wedge-chain geometry | The planar chain engine and its complete canonical cofacial star application are checked. The universal-source angle budget also supplies global kite separation and the complete retained-surface embedding. |
| Overall formalization effort completed | No reliable percentage. The previous 80% estimate and 65–90% range are withdrawn: the universal-source star construction is complete, but the remaining prism-with-diagonal branch is not. |
| Exact checked inventory | 992 Lean files; 4,544 audited theorem declarations including generated and private declarations. |

The 16 September, 16:42 UTC checkpoint checks **992 files / 4,544 audited
declarations**. These counts measure checked work, not the percentage of
the main theorem proved. The universal-source star embedding and its
whole-face edge-unfolding consequence are now complete. Arbitrary-source
singular junctions are outside that milestone. The main target's only
unfinished branch is the prism with a diagonal.
See [STAR_NEXT.md](STAR_NEXT.md) for the exact proved scope.

[OctahedronComplete](SixVertexUnfolding/OctahedronComplete.lean) proves the
complete original-edge octahedron case. A sharper pole and a maximum-curvature
slit discharge the local comparisons, both remote finite-cut exclusions,
Cases A and B, and both small-fan pocket contradictions.

The pocket proof constructs its interior seeds and whole protected patch.
The contained fan fixes the clockwise orientation; the four corners sum to
2π. Complementary petal-corner bounds and the exact curvature identities
then give the contradiction. This avoids introducing a separate six-sided
polygon after removing the patch. See
[OctahedralPocketContradiction](SixVertexUnfolding/Geometry/OctahedralPocketContradiction.lean)
and [POCKET_NEXT.md](POCKET_NEXT.md).

[MinusEdge](SixVertexUnfolding/MinusEdge.lean) completes the original
single-quadrilateral case. Two rigid placements agreeing across a flat diagonal
agree on the whole face. Identifying its two subdivision pieces preserves
connectivity, and a spanning tree uses only original hinges. The reassembled
whole facets inherit the proved triangle nonoverlap. The public definition of
an unfolding is unchanged.

[PrismComplete](SixVertexUnfolding/PrismComplete.lean) proves every ordinary
triangular prism using the general theorem in
[DomeComplete](SixVertexUnfolding/Geometry/DomeComplete.lean). Every pair of
whole outward petals is separated, including parallel and nonparallel base
hinges. The latter construction uses proved extended supporting planes and
virtual corner cones. No auxiliary point becomes a surface vertex or cut.

[PrismDiagonalRegions](SixVertexUnfolding/PrismDiagonalRegions.lean) proves
larger curvature regions for the prism with a diagonal: source 0 works when
κ₁ ≤ κ₀ and κ₂ ≤ max(κ₃, κ₄, κ₅); source 5 works when κ₄ ≤ κ₅ and
κ₃ ≤ max(κ₀, κ₁, κ₂). Either suffices. Equalities are included.

[SurfacePaths](SixVertexUnfolding/Geometry/SurfacePaths.lean) uses actual
continuous boundary paths and Mathlib total variation for arc length. Straight
face paths are shortest among all surface paths.
[StraightShortestPaths](SixVertexUnfolding/Geometry/StraightShortestPaths.lean)
proves that any shortest path between cofacial points stays on their straight
segment. [SixVertexStarCuts](SixVertexUnfolding/Geometry/SixVertexStarCuts.lean)
constructs the five-edge spanning cut tree at a universal vertex and proves
that its shortest cut segments meet only at the source. The complete
nonoverlapping star development after these cuts is now proved in
[UniversalStarEmbedding](SixVertexUnfolding/Geometry/UniversalStarEmbedding.lean),
and its whole-face consequence is in
[UniversalStarUnfolding](SixVertexUnfolding/Geometry/UniversalStarUnfolding.lean).

[ShortestSurfacePaths](SixVertexUnfolding/Geometry/ShortestSurfacePaths.lean)
now proves existence of finite shortest routes between arbitrary boundary
points, comparing with every continuous surface path. The proof reparameterizes
rectifiable curves and minimizes total variation on a compact family with a
common speed bound. [ShortestFaceSubdivision](SixVertexUnfolding/Geometry/ShortestFaceSubdivision.lean)
proves a finite subdivision into straight portions in whole original facets.
[ShortestSimplePaths](SixVertexUnfolding/Geometry/ShortestSimplePaths.lean)
supplies a constant-speed, injective shortest route for distinct endpoints.
[SHORTEST_PATHS.md](SHORTEST_PATHS.md) gives the short dependency map.
[LOCAL_GEODESICS.md](LOCAL_GEODESICS.md) maps the now-proved flat charts,
affine local continuation, and nonbranching results.

The six-vertex classification now has a geometric alternative to one use of
planarity. [QuadrilateralEdges](SixVertexUnfolding/Geometry/QuadrilateralEdges.lean)
proves the exact four-cycle on any quadrilateral facet's original vertices.
[FacetEdgeCounting](SixVertexUnfolding/Geometry/FacetEdgeCounting.lean) counts each
original edge twice, with arbitrary natural weights.
[ThreeByThreeExclusion](SixVertexUnfolding/Geometry/ThreeByThreeExclusion.lean)
uses these counts to exclude all nine cross-edges between two triples in the
remaining family without a universal vertex. This is a specific geometric
exclusion. Together with the subsequent finite and facet-incidence arguments,
it completes the classification of the remaining family without a universal vertex.

The main remaining proof obligation is the prism-with-diagonal branch:
geometric switch arguments, original-face comparisons, and original-edge
cut choices outside the already proved regions. Closing that branch will
eliminate the target theorem's last `sorry`.

The equivalence between the public retained dual hinge tree and cutting an
original-edge spanning tree to obtain an abstract disk is a separate
possible strengthening. It is not an additional hypothesis of the public
target, nor a gap in the completed universal-source star construction.

## Checking

The project pins Lean **4.29.1** and Mathlib commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`, with its dependency manifest included.
For an ordinary independent checkout:

```sh
lake exe cache get
lake build
lake env lean Statement.lean
```

The default build contains the proved library and [Audit.lean](Audit.lean).
The audit traverses the dependencies of every project declaration, including
private declarations, and rejects any
axiom other than `propext`, `Classical.choice`, and `Quot.sound`. It therefore
rejects `sorryAx`, including one hidden in a helper theorem, and extra axioms.
The unfinished `Statement.lean` is deliberately checked separately.

This pass used an existing installation read-only, without downloading or
modifying dependencies:

```sh
python3 check.py --dependencies /Users/sl/Dropbox/MyStuff/dev/lean-unfoldings
```

The checker verifies the Mathlib revision and compiles all local imports with
the pinned compiler and `autoImplicit=false`; outputs stay under this project's
ignored `.lake/` directory. It also checks the statement and runs the axiom audit.
The earlier six-hour session's clean rebuild checked **239 Lean files** and
accepted **1,510 project theorem declarations**. Its later additions were
compiled and audited incrementally. This continuation also compiled
all new and changed modules and their affected local dependents, followed by
the complete root import, target statement, and axiom audit. The final inventory
is recorded in the progress table above. This session rebuilt the core dependency chain after a local output was
refreshed, then checked all affected additions incrementally. It did not repeat
an independent clean installation.

The audit accepts only `propext`, `Classical.choice`, and `Quot.sound`.
The sole warning in the final root verification is the original `sorry` in
the unfinished target theorem. No numerical experiment or external certificate
is used as a Lean proof premise.
A previous independent negative control confirmed that an unused private extra axiom
is rejected; the temporary test fixture was then removed.
The independent dependency-download workflow above has not been exercised here.

For development, `--incremental` reuses local compiled files newer than their
sources and local imports. The earlier clean checkpoint used the command above without
that flag; this continuation used incremental verification.

## Annotated star-unfolding paper

[Interactive paper and Lean correspondence](star-paper/dist/index.html) covers
Kiazyk–Lubiw Sections 1.1–2. See [maintenance notes](star-paper/README.md) for
the fixed source snapshot and the distinction between checked restricted
results and the unfinished general theorem.
