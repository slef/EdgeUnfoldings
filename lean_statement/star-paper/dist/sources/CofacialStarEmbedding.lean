import SixVertexUnfolding.Geometry.StarOpenEmbedding
import SixVertexUnfolding.Geometry.StarLocalMetric
import SixVertexUnfolding.Geometry.StarBoundedImage
import SixVertexUnfolding.Geometry.RetainedCutConnectivity
import SixVertexUnfolding.Geometry.StarPolygonBoundary

/-! A proved, human-readable checkpoint for the star construction.
For a canonical six-vertex graph model with a vertex source sharing
a face with every vertex, the actual boundary minus the stated star cuts
has a bounded, connected, globally injective planar development preserving
its local intrinsic metric, with boundary a finite union of straight segments.
Extension to the universal-vertex family remains separate work. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

/-- The cofacial star has a bounded, connected, nonoverlapping development with polygonal boundary. -/
theorem cofacial_star_embedding {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (a : frontier P.body) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    ∃ develop : C(P.UncutSurface a, Plane),
      Topology.IsOpenEmbedding develop ∧ Bornology.IsBounded (range develop) ∧
      IsPathConnected (range develop) ∧
      (∃ edges : Finset (Plane × Plane), frontier (range develop) =
        ⋃ e ∈ edges, segment ℝ e.1 e.2) ∧
      ∀ b : P.UncutSurface a, ∃ radius > 0, ∀ c d : P.UncutSurface a,
        dist (c.val : Space) (b.val : Space) < radius →
        dist (d.val : Space) (b.val : Space) < radius →
        dist (develop c) (develop d) = P.surfaceDist c.val d.val := by
  obtain ⟨T⟩ := graph.exists_regular_cut_tree small_faces a
  obtain ⟨charts⟩ := graph.exists_cut_tree_charts small_faces a T cofacial
  let develop : C(P.UncutSurface a, Plane) :=
    ⟨fun b => charts.develop b.val, graph.develop_continuous small_faces charts cofacial⟩
  letI : PathConnectedSpace (P.UncutSurface a) := isPathConnected_iff_pathConnectedSpace.mp
    (graph.cofacial_uncut_surface_pathConnected small_faces a cofacial)
  exact ⟨develop, graph.develop_isOpenEmbedding small_faces charts source at_source cofacial,
    charts.develop_range_bounded, isPathConnected_range develop.continuous,
    ⟨charts.boundarySegments, graph.develop_frontier_eq_segments small_faces charts source at_source cofacial⟩,
    graph.develop_locally_isometric small_faces charts source at_source cofacial⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
