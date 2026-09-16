# Dome and ordinary-prism proofs: complete

The former two opposite-petal gaps are closed. The final theorems are
[DomeComplete.lean](SixVertexUnfolding/Geometry/DomeComplete.lean),
`Dome.hasEdgeUnfolding`, and
[PrismComplete.lean](SixVertexUnfolding/PrismComplete.lean),
`hasEdgeUnfolding_of_prism`. The dome theorem has no vertex-count bound.
The prism theorem imposes no parallelism or metric regularity.

## Proof map

1. [DomeDevelopment.lean](SixVertexUnfolding/Geometry/DomeDevelopment.lean)
   constructs the whole outward petals and original base hinge tree.
2. [DomeOppositePetals.lean](SixVertexUnfolding/Geometry/DomeOppositePetals.lean)
   splits according to whether the second facet's supporting height changes
   along the first hinge. Constant height forces parallel hinges, settled by
   [ParallelPetals.lean](SixVertexUnfolding/Geometry/ParallelPetals.lean).
   Otherwise an explicit affine parameter constructs their extended intersection.
3. [NormalizedFacetPlanes.lean](SixVertexUnfolding/Geometry/NormalizedFacetPlanes.lean)
   describes the whole extended facet planes by their supporting equations.
   [ThreeFacetPlanes.lean](SixVertexUnfolding/Geometry/ThreeFacetPlanes.lean)
   proves that three different facet planes meeting at a point have independent
   normals and permits arbitrary prescribed heights.
4. [DomeVirtualCorner.lean](SixVertexUnfolding/Geometry/DomeVirtualCorner.lean)
   constructs a point on the two petal planes strictly inside the base halfspace.
   Two support inequalities contain each whole facet in its virtual corner cone.
5. [ExtendedPetalSides.lean](SixVertexUnfolding/Geometry/ExtendedPetalSides.lean)
   extends outwardness beyond the polygons and reanchors it at the virtual
   corner. [ExtendedHinge.lean](SixVertexUnfolding/Geometry/ExtendedHinge.lean)
   and [PlacementRigidity.lean](SixVertexUnfolding/Geometry/PlacementRigidity.lean)
   supply exact hinge agreement and distances on the extended planes.
6. [MetricCornerCones.lean](SixVertexUnfolding/Geometry/MetricCornerCones.lean)
   separates both infinite cones by the bisector of the auxiliary apex copies.
7. An original edge belongs to only two facets, so a third facet misses one
   of its endpoints. This supplies the endpoint choices for every petal pair.
   [DomeComplete.lean](SixVertexUnfolding/Geometry/DomeComplete.lean) assembles
   the actual public unfolding.

The auxiliary points are used only for separators. They introduce no new
surface vertices, and all retained hinges are original edges. This implements
the extended-corner route of
[Pinciu, Theorem 1 and Corollary 2](https://cccg.ca/proceedings/2007/01a4.pdf),
with a distance-bisector argument for the cone separation.

## Remaining main-theorem work

The ordinary prism is no longer an open case. The exact remaining alternatives
are `unfolding_or_universal_or_prismDiagonal` in
[SixVertexRemaining.lean](SixVertexUnfolding/SixVertexRemaining.lean).
The unresolved shortest-path star nonoverlap theorem is used for both the
universal-vertex case and original-face comparisons in the prism-with-diagonal
switches. The shortest original cuts are now formalized in
[SurfacePaths.lean](SixVertexUnfolding/Geometry/SurfacePaths.lean) and
[SixVertexStarCuts.lean](SixVertexUnfolding/Geometry/SixVertexStarCuts.lean).
The cut-locus/kite partition and its nonoverlap argument are still absent.
