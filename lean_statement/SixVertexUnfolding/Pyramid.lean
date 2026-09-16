import SixVertexUnfolding.Geometry.PyramidPetal
import SixVertexUnfolding.Geometry.PyramidCertificate

/-!
The complete pyramid case: keep the original polygonal base whole and unfold
every triangular side outward along its original base edge.
-/

namespace SixVertexUnfolding

/-- Every convex pyramid, with any number of base vertices, has an original-edge unfolding. -/
theorem every_convex_pyramid_has_edge_unfolding (P : ConvexPolyhedron) (p : P.Pyramid) :
    P.HasEdgeUnfolding := by
  classical
  obtain ⟨left, left_rigid⟩ := p.base.exists_rigid_placement
  have placements (F : P.Face) : ∃ right : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ F.val, ∀ y ∈ F.val, dist (right x) (right y) = dist x y) ∧
      (∀ x : P.Vertex, (x : Space) ∈ F.val → (x : Space) ∈ p.base.val → right x = left x) ∧
      (F = p.base → right = left) ∧
      (F ≠ p.base → Disjoint (interior (left '' p.base.val)) (interior (right '' F.val)) ∧
        ∀ x : P.Vertex, (x : Space) ∈ p.base.val → (x : Space) ∉ F.val →
          dist (x : Space) p.apex < dist (left x) (right p.apex)) := by
    by_cases is_base : F = p.base
    · subst F
      exact ⟨left, left_rigid, fun _ _ _ => rfl, fun _ => rfl,
        fun impossible => False.elim (impossible rfl)⟩
    · obtain ⟨right, rigid, joined, safe, farther⟩ := p.exists_petal F is_base left left_rigid
      exact ⟨right, rigid, joined, fun equal => False.elim (is_base equal), fun _ => ⟨safe, farther⟩⟩
  choose copy rigid joined fixed_base petals using placements
  have base_copy : copy p.base = left := fixed_base p.base rfl
  apply p.unfolding_of_copies copy rigid
  · intro F x xF xB
    rw [base_copy]
    exact joined F x xF xB
  · intro F side
    rw [base_copy]
    exact (petals F side).1
  · intro F side x xB xF
    rw [base_copy]
    exact (petals F side).2 x xB xF

/-- A facet containing all but one original vertex is a pyramid base. -/
theorem has_edge_unfolding_of_large_face (P : ConvexPolyhedron) (base : P.Face)
    (one_missing : (base.val ∩ (P.vertices : Set Space)).ncard + 1 = P.vertices.card) :
    P.HasEdgeUnfolding := by
  obtain ⟨v, vertex, outside⟩ := base.exists_vertex_outside
  have base_vertices : base.val ∩ (P.vertices : Set Space) = (P.vertices : Set Space) \ {v} := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro x ⟨xB, xP⟩
      exact ⟨xP, fun same => outside (same ▸ xB)⟩
    · rw [Set.ncard_diff_singleton_of_mem vertex, Set.ncard_coe_finset]
      omega
    · exact P.vertices.finite_toSet.diff
  apply every_convex_pyramid_has_edge_unfolding P
  refine {
    base := base
    apex := ⟨v, vertex⟩
    apex_outside := outside
    other_vertices := ?_
  }
  intro x different
  have member : (x : Space) ∈ (P.vertices : Set Space) \ {v} :=
    ⟨x.property, fun same => different (Subtype.ext same)⟩
  rw [← base_vertices] at member
  exact member.1

/-- The five-vertex configuration with a quadrilateral facet is completely unfolded. -/
theorem every_five_vertex_polyhedron_with_quadrilateral_face (P : ConvexPolyhedron)
    (five_vertices : P.vertices.card = 5) (base : P.Face)
    (quadrilateral : (base.val ∩ (P.vertices : Set Space)).ncard = 4) :
    P.HasEdgeUnfolding := by
  apply has_edge_unfolding_of_large_face P base
  omega

/-- The six-vertex configuration with a pentagonal facet is completely unfolded. -/
theorem every_six_vertex_polyhedron_with_pentagonal_face (P : ConvexPolyhedron)
    (six_vertices : P.vertices.card = 6) (base : P.Face)
    (pentagon : (base.val ∩ (P.vertices : Set Space)).ncard = 5) :
    P.HasEdgeUnfolding := by
  apply has_edge_unfolding_of_large_face P base
  omega

end SixVertexUnfolding
