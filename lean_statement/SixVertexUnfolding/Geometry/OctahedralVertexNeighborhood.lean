import SixVertexUnfolding.Geometry.OctahedralCoverage
import SixVertexUnfolding.Geometry.OctahedralFanDevelopment
import SixVertexUnfolding.Geometry.EdgeHullSeparation

/-! The four actual fan triangles contain the whole surface near their pole. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- Convex hulls of named vertices contain no additional original vertex. -/
theorem vertex_mem_labeledHull_iff (v : Fin 6) (labels : Finset (Fin 6)) :
    (graph.vertex v : Space) ∈ graph.labeledHull labels ↔ v ∈ labels := by
  classical
  constructor
  · intro member
    by_contra absent
    apply P.vertex_not_mem_hull_others (graph.vertex v)
    apply convexHull_mono ?_ member
    rintro x ⟨w, hw, rfl⟩
    refine ⟨(graph.vertex w).property, ?_⟩
    intro equal
    exact absent (graph.vertex.injective (Subtype.ext equal) ▸ hw)
  · intro member
    exact subset_convexHull ℝ _ ⟨v, member, rfl⟩

theorem triangle_isCompact (t : Fin 8) : IsCompact (graph.triangle t) :=
  ((OctahedralTriangles.vertices t).finite_toSet.image (fun v => (graph.vertex v : Space))).isCompact_convexHull ℝ

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- The canonical eight triangles cover precisely the original surface. -/
theorem boundary_eq_triangles : frontier P.body = ⋃ t : Fin 8, graph.triangle t := by
  apply Subset.antisymm
  · intro x surface
    obtain ⟨F, on_face⟩ := P.boundary_point_in_face surface
    rw [graph.face_eq_subdivision_triangles small_faces F] at on_face
    obtain ⟨t, ht⟩ := mem_iUnion.mp on_face
    obtain ⟨_, triangle⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨t, triangle⟩
  · intro x member
    obtain ⟨t, ht⟩ := mem_iUnion.mp member
    exact (graph.triangleFace small_faces t).subset_frontier (graph.triangle_subset_face small_faces t ht)

include small_faces in
/-- No triangle not incident to the pole appears in a sufficiently small neighborhood. -/
theorem vertex_fan_neighborhood (pole : Fin 6) :
    ∃ U : Set Space, IsOpen U ∧ (graph.vertex pole : Space) ∈ U ∧
      U ∩ frontier P.body ⊆ ⋃ i : Fin 4, graph.triangle (fanTriangle pole i) := by
  let absent := {t : Fin 8 // pole ∉ OctahedralTriangles.vertices t}
  let forbidden : Set Space := ⋃ t : absent, graph.triangle t.val
  have closed : IsClosed forbidden := isClosed_iUnion_of_finite
    (fun t => (graph.triangle_isCompact t.val).isClosed)
  refine ⟨forbiddenᶜ, closed.isOpen_compl, ?_, ?_⟩
  · intro member
    obtain ⟨t, ht⟩ := mem_iUnion.mp member
    exact t.property ((graph.vertex_mem_labeledHull_iff pole _).mp ht)
  · rintro x ⟨near, surface⟩
    rw [graph.boundary_eq_triangles small_faces] at surface
    obtain ⟨t, ht⟩ := mem_iUnion.mp surface
    have incident : pole ∈ OctahedralTriangles.vertices t := by
      by_contra absent_t
      exact near (mem_iUnion.mpr ⟨⟨t, absent_t⟩, ht⟩)
    have exhaust : ∀ (v : Fin 6) (t : Fin 8), v ∈ OctahedralTriangles.vertices t →
        ∃ i : Fin 4, fanTriangle v i = t := by decide
    obtain ⟨i, rfl⟩ := exhaust pole t incident
    exact mem_iUnion.mpr ⟨i, ht⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
