import SixVertexUnfolding.Geometry.SourceBisectorDensity
import SixVertexUnfolding.Geometry.PlacedTriangle

/-! Removing finitely many straight segments leaves a dense subset of
the actual polyhedral boundary. The proof works in a whole original facet
even when the neighborhood is centered on an edge or a vertex. -/

namespace SixVertexUnfolding

open Set

theorem planar_segment_interior_empty (a b : Plane) : interior (segment ℝ a b) = ∅ := by
  by_cases same : a = b
  · simp [same]
  let normal : Plane := !₂[-(b 1 - a 1), b 0 - a 0]
  have nonzero : normal ≠ 0 := by
    intro zero
    apply same
    have first := congrArg (fun x : Plane => x 0) zero
    have second := congrArg (fun x : Plane => x 1) zero
    simp only [normal, PiLp.zero_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at first second
    ext i
    fin_cases i
    · change a 0 = b 0
      linarith
    · change a 1 = b 1
      linarith
  have equal : inner ℝ normal b = inner ℝ normal a := by
    simp only [plane_inner_coordinates, normal, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have contained : segment ℝ a b ⊆ {x | inner ℝ normal x = inner ℝ normal a} := by
    intro x hx
    have mapped := mem_image_of_mem (innerSL ℝ normal).toLinearMap.toAffineMap hx
    rw [image_segment] at mapped
    change inner ℝ normal x ∈ segment ℝ (inner ℝ normal a) (inner ℝ normal b) at mapped
    simpa only [equal, segment_same, mem_singleton_iff] using mapped
  exact subset_empty_iff.mp ((interior_mono contained).trans_eq (line_interior_empty normal nonzero _))

/-- A finite collection of planar segments is closed and has empty interior. -/
theorem finite_planar_segments_empty {ι : Type*} [Finite ι] (p q : ι → Plane) :
    IsClosed (⋃ i, segment ℝ (p i) (q i)) ∧ interior (⋃ i, segment ℝ (p i) (q i)) = ∅ := by
  have closed (i : ι) : IsClosed (segment ℝ (p i) (q i)) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image
      (AffineMap.lineMap (p i) (q i) : ℝ →ᵃ[ℝ] Plane).continuous_of_finiteDimensional).isClosed
  refine ⟨isClosed_iUnion_of_finite closed, ?_⟩
  have empty := finite_closed_sUnion_interior_empty (range (fun i => segment ℝ (p i) (q i)))
    (finite_range _) (by rintro _ ⟨i, rfl⟩; exact closed i)
    (by rintro _ ⟨i, rfl⟩; exact planar_segment_interior_empty _ _)
  simpa only [sUnion_range] using empty

namespace ConvexPolyhedron

/-- Finite straight-line obstacles cannot fill a relative surface neighborhood. -/
theorem finite_segments_complement_dense (P : ConvexPolyhedron) {ι : Type*} [Finite ι]
    (p q : ι → Space) : Dense {b : frontier P.body | ∀ i, (b : Space) ∉ segment ℝ (p i) (q i)} := by
  intro b
  apply mem_closure_iff.mpr
  intro U openU bU
  obtain ⟨ε, positive, contained⟩ := Metric.isOpen_iff.mp openU b bU
  obtain ⟨F, bF⟩ := P.boundary_point_in_face b.property
  let place := P.faceCoordinates F
  let bad : Set Plane := ⋃ i, segment ℝ (place (p i)) (place (q i))
  have dense : Dense badᶜ := interior_eq_empty_iff_dense_compl.mp
    (finite_planar_segments_empty (fun i => place (p i)) (fun i => place (q i))).2
  have center : place b ∈ closure (interior (place '' F.val)) := by
    rw [F.placed_face_regular place (P.faceCoordinates_rigid F)]
    exact ⟨b, bF, rfl⟩
  have openV : IsOpen (Metric.ball (place b) ε ∩ interior (place '' F.val)) :=
    Metric.isOpen_ball.inter isOpen_interior
  have nonempty : (Metric.ball (place b) ε ∩ interior (place '' F.val)).Nonempty := by
    obtain ⟨z, near, inside⟩ := mem_closure_iff.mp center (Metric.ball (place b) ε)
      Metric.isOpen_ball (Metric.mem_ball_self positive)
    exact ⟨z, near, inside⟩
  obtain ⟨z, outside, near⟩ := dense.exists_mem_open openV nonempty
  obtain ⟨x, xF, at_z⟩ := interior_subset near.2
  let c : frontier P.body := ⟨x, F.subset_frontier xF⟩
  refine ⟨c, contained ?_, ?_⟩
  · change dist x (b : Space) < ε
    rw [← P.faceCoordinates_rigid F x xF b bF]
    exact at_z ▸ near.1
  · intro i member
    apply outside
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← at_z]
    have mapped := mem_image_of_mem place member
    rwa [image_segment] at mapped

end ConvexPolyhedron
end SixVertexUnfolding
