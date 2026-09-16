# Checked assembly of the cofacial star

Current status: 16 September 2026. This construction is proved for the
cofacial vertex sources satisfying `CofacialStarEmbedding`'s canonical
nonuniversal graph hypotheses. Extension to universal-vertex solids and
arbitrary-source singular junctions is unfinished.

## Actual pieces and one placement

Each oriented cut-tree edge carries its two actual closed radial triangles,
including their complete surface homeomorphisms. Source copies remain
labelled. Cofaciality makes all original nonsource cut-tree vertices leaves;
internal junctions have the actual flat fan.

Frames propagate along the tree. Opposite edge orientations have a proved
fixed rigid transition and source-label correspondence. Every pair of
unoriented tree edges is joined by a simple tree path. The actual source
angle budget and coherent wedge transitions separate their kites in this
one global plane. No numerical angle budget is supplied by the caller.

## Retained surface

All triangle maps agree at every shared surface point outside the explicit
source-to-original-vertex cuts. Their finite closed cover gives a continuous
global map. True inverse disks are constructed in triangle interiors,
open cut-edge bases, retained endpoint rays, and internal junctions.
These give global injectivity, openness, and exact local intrinsic isometry.

Each retained point follows its ray to a nonoriginal cut point. The cut
tree with its original leaves removed remains connected, so the retained
surface and its planar image are path connected. The image is bounded by
the finite compact kite union.

## Closure and cut copies

Every open triangle is in the actual developed image. The closure of that
image is exactly the closed-kite union. A represented triangle point is
in the open image exactly when its surface point is uncut, and it is on
the planar boundary exactly when its surface point is cut. The proof uses
the actual continuous inverse disks, including at triangle boundaries.

The cut part of a triangle is its source copy and the full radial sides
ending at original vertices. Collecting these sides gives the exact finite
straight-segment boundary. Degenerate segments preserve source copies;
no simplicity of the entire boundary curve is silently asserted.

The compact readable checkpoint is
[CofacialStarEmbedding.lean](SixVertexUnfolding/Geometry/CofacialStarEmbedding.lean).
The precise boundary theorem is
[StarPolygonBoundary.lean](SixVertexUnfolding/Geometry/StarPolygonBoundary.lean).

## Whole original faces and hinges

[StarEdgeAssembly.lean](SixVertexUnfolding/Geometry/StarEdgeAssembly.lean)
proves a generic conversion to the unchanged public `EdgeUnfolding`.
Its inputs are a continuous injective local intrinsic isometry, connectivity
of the retained surface, and cuts avoiding the original face interiors.

Local planar rigidity gives one affine rigid placement per whole face.
Density and continuity extend agreement to retained face boundaries.
Injectivity excludes overlapping face interiors. The finite closed face
cover gives a connected graph of retained original hinges; choose a
spanning tree. A retained point on an original edge forces its whole open
edge to be retained, and continuity gives agreement at both original endpoints.

Accidental planar boundary contacts are permitted by the public definition.
The proof does not require unrelated boundary copies to have identical
original preimages.

## Remaining geometry

The generic conversion does not construct a universal-source development.
The universal five-cycle, actual supported five-ray figure, and complete
local surface coverage and strict total-angle bound are now proved.
The local angle bounds, shorter detours, and shortest-route avoidance are
now proved at every original vertex, without a canonical graph premise,
for any polyhedron with at most six vertices and triangular or quadrilateral
faces. Finite normalized route fibers, nonbranching, finite source-image
formulas, and the exact finite cut tree now also hold in this larger scope.
The cut set is proved compact and contractible, its embedded graph is a
tree, and subdivision at all junctions and original vertices leaves exactly
two routes inside each open edge. These results allow arbitrary surface
sources. The radial triangles and whole-surface coverage now use these
broader inputs. For a cofacial source, original cut vertices are proved
leaves, and the complete `CutTreeCharts` collection is constructed. Local
cone coverage and the flat-junction full-turn sum are also checked without
a canonical graph. Global curvature accounting, the resulting source-angle
budget, and the transfer of nonoverlap/gluing remain unfinished.
See [STAR_NEXT.md](STAR_NEXT.md) for the exact next obligation and scope.
