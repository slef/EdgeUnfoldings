import SixVertexUnfolding.Geometry.TetrahedronPetal
import SixVertexUnfolding.Geometry.TetrahedronCertificate

/-!
The complete four-vertex case. Place one base triangle, unfold the three other
triangles outward, and separate their interiors using the source-copy bisectors.
-/

namespace SixVertexUnfolding

/-- Every solid convex polyhedron with four genuine vertices has an original-edge unfolding. -/
theorem every_convex_polyhedron_with_four_vertices (P : ConvexPolyhedron)
    (four_vertices : P.vertices.card = 4) : P.HasEdgeUnfolding := by
  classical
  obtain ⟨s, vertex⟩ := P.vertices_nonempty
  let source : P.Vertex := ⟨s, vertex⟩
  let base := P.oppositeFace four_vertices source
  obtain ⟨left, left_rigid⟩ := base.exists_rigid_placement
  have placements (v : P.Vertex) : ∃ right : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ (P.oppositeFace four_vertices v).val,
        ∀ y ∈ (P.oppositeFace four_vertices v).val, dist (right x) (right y) = dist x y) ∧
      (∀ x : P.Vertex, x ≠ source → x ≠ v → right x = left x) ∧
      (v = source → right = left) ∧
      (v ≠ source →
        Disjoint (interior (left '' base.val))
          (interior (right '' (P.oppositeFace four_vertices v).val)) ∧
        dist (v : Space) source < dist (left v) (right source)) := by
    by_cases same : v = source
    · subst v
      exact ⟨left, left_rigid, fun _ _ _ => rfl, fun _ => rfl, fun impossible => False.elim (impossible rfl)⟩
    · obtain ⟨right, rigid, joined, safe, farther⟩ :=
        P.exists_tetrahedron_petal four_vertices source v same left left_rigid
      exact ⟨right, rigid, joined, fun equal => False.elim (same equal), fun _ => ⟨safe, farther⟩⟩
  choose copy rigid joined fixed_base petals using placements
  have base_copy : copy source = left := fixed_base source rfl
  apply P.tetrahedron_unfolding_of_copies four_vertices source copy rigid
  · intro v x xs xv
    rw [base_copy]
    exact joined v x xs xv
  · intro v different
    rw [base_copy]
    exact (petals v different).1
  · intro v different
    rw [base_copy]
    exact (petals v different).2

end SixVertexUnfolding
