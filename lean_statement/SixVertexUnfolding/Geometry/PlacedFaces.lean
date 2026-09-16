import SixVertexUnfolding.Geometry.PlacementRigidity
import SixVertexUnfolding.Geometry.Separation

/-! A rigid affine placement of a facet produces a genuine two-dimensional planar polygon. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Rigidity makes the image of a facet span the target plane. -/
theorem placed_face_spans_plane (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) :
    affineSpan ℝ (place '' F.val) = ⊤ := by
  let D := (affineSpan ℝ F.val).direction
  let L : D →ₗ[ℝ] Plane := place.linear.comp D.subtype
  obtain ⟨a, ha⟩ := F.nonempty
  have a_span := subset_affineSpan ℝ F.val ha
  have lift_in_span (u : D) : (u : Space) + a ∈ affineSpan ℝ F.val :=
    AffineSubspace.vadd_mem_of_mem_direction u.property a_span
  have formula (u : D) : place ((u : Space) + a) = L u + place a := place.map_vadd a u
  have span_rigid := affine_rigid_on_span_of_distances place F.val F.nonempty rigid

  -- The linear part is injective on the two-dimensional direction space, hence onto the plane.
  have injective : Function.Injective L := by
    intro u v equal
    have equal_images : place ((u : Space) + a) = place ((v : Space) + a) := by
      rw [formula, formula, equal]
    have distance := span_rigid ((u : Space) + a) (lift_in_span u)
      ((v : Space) + a) (lift_in_span v)
    rw [equal_images, dist_self] at distance
    apply Subtype.ext
    exact add_right_cancel (dist_eq_zero.mp distance.symm)
  have dimension : Module.finrank ℝ D = Module.finrank ℝ Plane := by
    have face_dimension := F.property.1
    simpa only [Plane, finrank_euclideanSpace_fin] using face_dimension
  have onto := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dimension).mp injective
  rw [← AffineSubspace.map_span]
  apply top_unique
  intro z _
  obtain ⟨u, hu⟩ := onto (z - place a)
  exact ⟨(u : Space) + a, lift_in_span u, by rw [formula, hu, sub_add_cancel]⟩

/-- The nonoverlap test uses nonempty, ordinary two-dimensional interiors. -/
theorem placed_face_interior_nonempty (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) :
    (interior (place '' F.val)).Nonempty := by
  apply (F.convex.affine_image place).interior_nonempty_iff_affineSpan_eq_top.mpr
  exact F.placed_face_spans_plane place rigid

/-- For rigid affine placements, a vertex separator is equivalent to disjoint face interiors. -/
theorem nonoverlap_iff_vertex_separator (G : P.Face) (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ G.val, ∀ y ∈ G.val, dist (right x) (right y) = dist x y) :
    Disjoint (interior (left '' F.val)) (interior (right '' G.val)) ↔
      ∃ height : Plane →L[ℝ] ℝ, Function.Surjective height ∧ ∃ level : ℝ,
        (∀ x ∈ F.val ∩ (P.vertices : Set Space), height (left x) ≤ level) ∧
        (∀ x ∈ G.val ∩ (P.vertices : Set Space), level ≤ height (right x)) := by
  constructor
  · intro nonoverlap
    have right_convex := G.convex.affine_image right
    have right_interior := G.placed_face_interior_nonempty right right_rigid
    have separated_closure := nonoverlap.closure_right isOpen_interior
    rw [right_convex.closure_interior_eq_closure_of_nonempty_interior right_interior]
      at separated_closure
    obtain ⟨height, level, nonzero, upper, lower⟩ :=
      geometric_hahn_banach_of_nonempty_interior (F.convex.affine_image left) right_convex
        (separated_closure.mono_right subset_closure)
        (F.placed_face_interior_nonempty left left_rigid) (G.nonempty.image right)
    have onto : Function.Surjective height := by
      have some_nonzero : ∃ x, height x ≠ 0 := by
        by_contra all_zero
        push Not at all_zero
        exact nonzero (ContinuousLinearMap.ext all_zero)
      obtain ⟨x, hx⟩ := some_nonzero
      intro r
      refine ⟨(r / height x) • x, ?_⟩
      rw [map_smul]
      exact div_mul_cancel₀ r hx
    exact ⟨height, onto, level,
      fun x hx => upper (left x) (Set.mem_image_of_mem left hx.1),
      fun x hx => lower (right x) (Set.mem_image_of_mem right hx.1)⟩
  · rintro ⟨height, onto, level, upper, lower⟩
    apply disjoint_interiors_of_halfplanes height onto level
    · rintro _ ⟨x, hx, rfl⟩
      exact F.upper_bound_of_vertices left height level upper x hx
    · rintro _ ⟨x, hx, rfl⟩
      exact G.lower_bound_of_vertices right height level lower x hx

end SixVertexUnfolding.ConvexPolyhedron.Face
