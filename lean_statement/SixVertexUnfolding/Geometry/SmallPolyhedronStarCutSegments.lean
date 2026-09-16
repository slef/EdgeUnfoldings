import SixVertexUnfolding.Geometry.StarCutSegments
import SixVertexUnfolding.Geometry.SmallPolyhedronStarCutParameters

/-! In each developed triangle the removed part is a finite union of
whole straight sides, with a degenerate segment for the source copy.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- Exactly the listed segments are images of removed triangle points. -/
theorem small_triangle_cut_image {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (side : Bool) (x : Plane) :
    (∃ s t : unitInterval, D.routes side s t ∈ P.starCuts a ∧
      triangleFanMap (D.motion (D.apex side)) (D.motion D.model.left) (D.motion D.model.right) (s, t) = x) ↔
    ∃ e ∈ D.cutSegments side, x ∈ segment ℝ e.1 e.2 := by
  rw [D.mem_cutSegments_union]
  constructor
  · rintro ⟨s, t, cut, value⟩
    rcases (small_triangle_ray_cut_iff size small_faces D cofacial side s t).mp cut with zero | left | right
    · subst t
      exact Or.inl (by simpa [triangleFanMap] using value.symm)
    · obtain ⟨rfl, original⟩ := left
      refine Or.inr (Or.inl ⟨original, ?_⟩)
      rw [segment_eq_image_lineMap]
      exact ⟨t, t.property, by simpa [triangleFanMap] using value⟩
    · obtain ⟨rfl, original⟩ := right
      refine Or.inr (Or.inr ⟨original, ?_⟩)
      rw [segment_eq_image_lineMap]
      exact ⟨t, t.property, by simpa [triangleFanMap] using value⟩
  · rintro (at_source | ⟨original, on_left⟩ | ⟨original, on_right⟩)
    · refine ⟨0, 0, (small_triangle_ray_cut_iff size small_faces D cofacial side 0 0).mpr (Or.inl rfl), ?_⟩
      simpa [triangleFanMap] using at_source.symm
    · rw [segment_eq_image_lineMap] at on_left
      obtain ⟨t, unit, value⟩ := on_left
      refine ⟨0, ⟨t, unit⟩,
        (small_triangle_ray_cut_iff size small_faces D cofacial side 0 ⟨t, unit⟩).mpr (Or.inr (Or.inl ⟨rfl, original⟩)), ?_⟩
      simpa [triangleFanMap] using value
    · rw [segment_eq_image_lineMap] at on_right
      obtain ⟨t, unit, value⟩ := on_right
      refine ⟨1, ⟨t, unit⟩,
        (small_triangle_ray_cut_iff size small_faces D cofacial side 1 ⟨t, unit⟩).mpr (Or.inr (Or.inr ⟨rfl, original⟩)), ?_⟩
      simpa [triangleFanMap] using value

end SixVertexUnfolding.ConvexPolyhedron
