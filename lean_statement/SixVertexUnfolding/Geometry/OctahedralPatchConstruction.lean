import SixVertexUnfolding.Geometry.OctahedralPatchSpan

/-! The metric patch model is realized by rigid placements of the actual original facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- Any rigid placement of a fan facet extends to its outward petal patch. -/
theorem exists_patch_of_fan_placement (source : Fin 6) (sector : Fin 4) (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ (graph.triangleFace small_faces (fanTriangle (opposite source) sector)).val,
      ∀ y ∈ (graph.triangleFace small_faces (fanTriangle (opposite source) sector)).val,
        dist (place x) (place y) = dist x y) :
    ∃ patch : graph.DevelopedPatch source sector,
      patch.pole = place (graph.vertex (opposite source)) ∧
      patch.left = place (graph.vertex (fanNeighbor source sector)) ∧
      patch.right = place (graph.vertex (fanNeighbor source (sector + 1))) := by
  let a : Space := graph.vertex (fanNeighbor source sector)
  let b : Space := graph.vertex (fanNeighbor source (sector + 1))
  let w : Space := graph.vertex (opposite source)
  let v : Space := graph.vertex source
  let fan := graph.triangleFace small_faces (fanTriangle (opposite source) sector)
  let petal := graph.triangleFace small_faces (fanTriangle source sector)
  have paired : ∀ s i, fanNeighbor (opposite s) i = fanNeighbor s i := by decide
  have aF : a ∈ fan.val := graph.fan_sector_on_face (opposite source) small_faces sector _ (by simp [paired])
  have bF : b ∈ fan.val := graph.fan_sector_on_face (opposite source) small_faces sector _ (by simp [paired])
  have wF : w ∈ fan.val := graph.fan_sector_on_face (opposite source) small_faces sector _ (by simp)
  have aP : a ∈ petal.val := graph.fan_sector_on_face source small_faces sector _ (by simp)
  have bP : b ∈ petal.val := graph.fan_sector_on_face source small_faces sector _ (by simp)
  have vP : v ∈ petal.val := graph.fan_sector_on_face source small_faces sector _ (by simp)
  have ab : a ≠ b := fun same => DevelopedPatch.equator_distinct (graph.vertex.injective (Subtype.ext same))
  have flat_ab : place a ≠ place b := by
    intro same
    have length := rigid a aF b bF
    rw [same, dist_self] at length
    exact ab (dist_eq_zero.mp length.symm)
  obtain ⟨right, right_rigid, at_a, at_b, outward⟩ := petal.exists_outward_placement a b w v aP bP place
    (rigid a aF b bF) flat_ab
  refine ⟨{
    pole := place w
    left := place a
    right := place b
    apex := right v
    hinge_length := rigid a aF b bF
    fan_left := rigid w wF a aF
    fan_right := rigid w wF b bF
    petal_left := ?_
    petal_right := ?_
    outward := outward
  }, rfl, rfl, rfl⟩
  · rw [← at_a]
    exact right_rigid v vP a aP
  · rw [← at_b]
    exact right_rigid v vP b bP

include small_faces in
/-- Every actual fan sector has an outward two-triangle development. -/
theorem exists_developed_patch (source : Fin 6) (sector : Fin 4) :
    Nonempty (graph.DevelopedPatch source sector) := by
  obtain ⟨place, rigid⟩ := (graph.triangleFace small_faces (fanTriangle (opposite source) sector)).exists_rigid_placement
  obtain ⟨patch, _⟩ := graph.exists_patch_of_fan_placement small_faces source sector place rigid
  exact ⟨patch⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
