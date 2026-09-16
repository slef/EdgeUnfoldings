import SixVertexUnfolding.Geometry.FiniteCutSegments

/-! The exact finite segment description presents the actual cut set
as a continuous quotient of finitely many compact intervals. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The interval presentation covers precisely the actual cut set, with its existing topology. -/
theorem cutSet_interval_presentation (a : frontier P.body) :
    ∃ segments : Set P.FaceSegment, segments.Finite ∧
      ∃ f : (Σ _ : segments, unitInterval) → P.cutSetInSpace a, Continuous f ∧ Function.Surjective f := by
  obtain ⟨segments, finite, exact_segments⟩ := graph.cutSet_finite_segments small_faces a
  have on_cut (s : segments) (t : unitInterval) :
      AffineMap.lineMap s.val.first s.val.last (t : ℝ) ∈ P.cutSetInSpace a := by
    rw [exact_segments]
    refine mem_iUnion.mpr ⟨s.val, mem_iUnion.mpr ⟨s.property, ?_⟩⟩
    rw [FaceSegment.points, segment_eq_image_lineMap]
    exact ⟨t, t.property, rfl⟩
  let f : (Σ _ : segments, unitInterval) → P.cutSetInSpace a :=
    fun pair => ⟨AffineMap.lineMap pair.1.val.first pair.1.val.last (pair.2 : ℝ), on_cut pair.1 pair.2⟩
  refine ⟨segments, finite, f, ?_, ?_⟩
  · apply continuous_sigma
    intro s
    let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap s.val.first s.val.last
    exact (line.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _
  · intro x
    have member := (Set.ext_iff.mp exact_segments (x : Space)).mp x.property
    obtain ⟨s, member⟩ := mem_iUnion.mp member
    obtain ⟨hs, on_segment⟩ := mem_iUnion.mp member
    rw [FaceSegment.points, segment_eq_image_lineMap] at on_segment
    obtain ⟨t, ht, equal⟩ := on_segment
    exact ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, Subtype.ext equal⟩

include graph small_faces in
/-- The cut set is locally path connected, including at original vertices and junctions. -/
theorem cutSet_locally_path_connected (a : frontier P.body) : LocPathConnectedSpace (P.cutSetInSpace a) := by
  obtain ⟨segments, finite, f, continuous_f, surjective_f⟩ := graph.cutSet_interval_presentation small_faces a
  letI : Finite segments := finite
  letI : LocPathConnectedSpace unitInterval :=
    (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).locPathConnectedSpace
  exact (IsQuotientMap.of_surjective_continuous surjective_f continuous_f).locPathConnectedSpace

include graph small_faces in
/-- The entire cut set has only finitely many connected components. Connectivity itself is a later obligation. -/
theorem cutSet_finite_connected_components (a : frontier P.body) : Finite (ConnectedComponents (P.cutSetInSpace a)) := by
  letI : LocPathConnectedSpace (P.cutSetInSpace a) := graph.cutSet_locally_path_connected small_faces a
  letI : CompactSpace (P.cutSetInSpace a) := isCompact_iff_compactSpace.mp (graph.cutSetInSpace_compact small_faces a)
  infer_instance

include graph small_faces in
/-- The connected components also coincide with path components and are finite in number. -/
theorem cutSet_finite_path_components (a : frontier P.body) : Finite (ZerothHomotopy (P.cutSetInSpace a)) := by
  letI : LocPathConnectedSpace (P.cutSetInSpace a) := graph.cutSet_locally_path_connected small_faces a
  letI : CompactSpace (P.cutSetInSpace a) := isCompact_iff_compactSpace.mp (graph.cutSetInSpace_compact small_faces a)
  infer_instance

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
