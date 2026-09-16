import SixVertexUnfolding.Geometry.StarLocalMetric
import SixVertexUnfolding.Geometry.RetainedFaceContinuity

/-! The actual star development determines rigid placements of original
faces whose interiors contain no star cuts. Agreement includes retained
boundary points, which will determine the joins between faces. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

/-- Every original face with uncut interior has one rigid placement agreeing with the star map. -/
theorem develop_whole_face {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (F : P.Face)
    (uncut : ∀ (x : Space) (hx : x ∈ F.val),
      P.faceCoordinates F x ∈ interior (P.faceCoordinates F '' F.val) →
      (⟨x, F.subset_frontier hx⟩ : frontier P.body) ∉ P.starCuts a) :
    ∃ place : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) ∧
      ∀ b : P.UncutSurface a, (b.val : Space) ∈ F.val → place b.val = charts.develop b.val := by
  let develop : C(P.UncutSurface a, Plane) :=
    ⟨fun b => charts.develop b.val, graph.develop_continuous small_faces charts cofacial⟩
  obtain ⟨place, rigid, agrees⟩ := uncut_face_rigid_placement develop
    (graph.develop_locally_isometric small_faces charts source at_source cofacial) F uncut
  exact ⟨place, rigid, F.agrees_on_retained_face develop place agrees⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
