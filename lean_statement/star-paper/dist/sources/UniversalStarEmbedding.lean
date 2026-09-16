import SixVertexUnfolding.Geometry.UniversalStarKiteSeparation
import SixVertexUnfolding.Geometry.SmallPolyhedronStarOpenEmbedding
import SixVertexUnfolding.Geometry.SmallPolyhedronStarLocalMetric
import SixVertexUnfolding.Geometry.SmallPolyhedronRetainedCutConnectivity
import SixVertexUnfolding.Geometry.SmallPolyhedronStarPolygonBoundary
import SixVertexUnfolding.Geometry.StarBoundedImage

/-! The star theorem for the remaining six-vertex universal-source family.
The cut tree, charts, nonoverlap, gluing, inverse disks, local metric,
connectivity, and polygonal boundary are all constructed from the solid.
The source is an original vertex adjacent to every other original vertex.
This is not the arbitrary-source star theorem. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Cutting the five edges from a universal vertex gives a bounded,
connected, nonoverlapping star development with polygonal boundary. -/
theorem universal_star_embedding {P : ConvexPolyhedron} (six : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (a : frontier P.body) (source : P.Vertex) (at_source : (a : Space) = (source : Space))
    (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    ∃ develop : C(P.UncutSurface a, Plane),
      Topology.IsOpenEmbedding develop ∧ Bornology.IsBounded (range develop) ∧
      IsPathConnected (range develop) ∧
      (∃ edges : Finset (Plane × Plane), frontier (range develop) =
        ⋃ e ∈ edges, segment ℝ e.1 e.2) ∧
      ∀ b : P.UncutSurface a, ∃ radius > 0, ∀ c d : P.UncutSurface a,
        dist (c.val : Space) (b.val : Space) < radius →
        dist (d.val : Space) (b.val : Space) < radius →
        dist (develop c) (develop d) = P.surfaceDist c.val d.val := by
  have size : P.vertices.card ≤ 6 := by omega
  have cofacial := universal_source_cofacial a source at_source universal
  obtain ⟨T⟩ := small_exists_regular_cut_tree size small_faces a
  obtain ⟨charts, separated⟩ :=
    universal_exists_separated_cut_tree_charts six small_faces T source universal at_source
  let develop : C(P.UncutSurface a, Plane) :=
    ⟨fun b => charts.develop b.val, small_develop_continuous size small_faces charts cofacial⟩
  letI : PathConnectedSpace (P.UncutSurface a) := isPathConnected_iff_pathConnectedSpace.mp
    (small_cofacial_uncut_surface_pathConnected size small_faces a cofacial)
  exact ⟨develop, small_develop_isOpenEmbedding size small_faces charts separated cofacial,
    charts.develop_range_bounded, isPathConnected_range develop.continuous,
    ⟨charts.boundarySegments, small_develop_frontier_eq_segments size small_faces charts separated cofacial⟩,
    small_develop_locally_isometric size small_faces charts separated cofacial⟩

end SixVertexUnfolding.ConvexPolyhedron
