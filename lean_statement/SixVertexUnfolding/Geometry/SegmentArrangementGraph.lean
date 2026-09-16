import SixVertexUnfolding.Geometry.SegmentArrangementVertices
import SixVertexUnfolding.Geometry.FiniteIntervalNeighbors

/-! A finite graph obtained by subdividing a finite segment collection
at all endpoints and crossings. Its straight edge traces cover exactly
the original segments. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Consecutive subdivision vertices on one of the given straight segments. -/
def segmentGraph {P : ConvexPolyhedron} (segments : Set P.FaceSegment) :
    SimpleGraph (segmentVertices segments) where
  Adj a b := a ≠ b ∧
    (∃ s ∈ segments, (a : Space) ∈ s.points ∧ (b : Space) ∈ s.points) ∧
    Disjoint (openSegment ℝ (a : Space) (b : Space)) (segmentVertices segments)
  symm := by
    intro a b h
    refine ⟨h.1.symm, ?_, ?_⟩
    · obtain ⟨s, hs, ha, hb⟩ := h.2.1
      exact ⟨s, hs, hb, ha⟩
    · rw [openSegment_symm]
      exact h.2.2
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem segmentGraph_edge_covered {P : ConvexPolyhedron} (segments : Set P.FaceSegment)
    {a b : segmentVertices segments} (edge : (segmentGraph segments).Adj a b) :
    segment ℝ (a : Space) (b : Space) ⊆ ⋃ s ∈ segments, s.points := by
  obtain ⟨s, hs, ha, hb⟩ := edge.2.1
  intro x hx
  exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, s.convex.segment_subset ha hb hx⟩⟩

/-- Any point not itself a subdivision vertex lies inside a graph edge. -/
theorem segmentGraph_covers_nonvertex {P : ConvexPolyhedron} (segments : Set P.FaceSegment)
    (finite : segments.Finite) {x : Space} (member : x ∈ ⋃ s ∈ segments, s.points)
    (not_vertex : x ∉ segmentVertices segments) :
    ∃ a b : segmentVertices segments, (segmentGraph segments).Adj a b ∧
      x ∈ openSegment ℝ (a : Space) (b : Space) := by
  obtain ⟨s, member⟩ := mem_iUnion.mp member
  obtain ⟨hs, on_segment⟩ := mem_iUnion.mp member
  have first_vertex : s.first ∈ segmentVertices segments := Or.inl (Or.inl ⟨s, hs, rfl⟩)
  have last_vertex : s.last ∈ segmentVertices segments := Or.inl (Or.inr ⟨s, hs, rfl⟩)
  have different : s.first ≠ s.last := by
    intro same
    have equal : x = s.first := by simpa [FaceSegment.points, same] using on_segment
    exact not_vertex (equal ▸ first_vertex)
  let curve : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap s.first s.last
  have injective : Function.Injective curve := AffineMap.lineMap_injective ℝ different
  let parameters : Set ℝ := curve ⁻¹' segmentVertices segments
  have finite_parameters : parameters.Finite := (segmentVertices_finite segments finite).preimage injective.injOn
  have zero : (0 : ℝ) ∈ parameters := by
    simpa only [parameters, mem_preimage, curve, AffineMap.lineMap_apply_zero] using first_vertex
  have one : (1 : ℝ) ∈ parameters := by
    simpa only [parameters, mem_preimage, curve, AffineMap.lineMap_apply_one] using last_vertex
  rw [FaceSegment.points, segment_eq_image_lineMap] at on_segment
  obtain ⟨t, ht, equal⟩ := on_segment
  have t_not : t ∉ parameters := by
    change curve t ∉ segmentVertices segments
    rw [show curve t = x from equal]
    exact not_vertex
  obtain ⟨u, hu, v, hv, ut, tv, lower, upper, consecutive⟩ :=
    finite_interval_neighbors parameters finite_parameters zero one ht t_not
  let a : segmentVertices segments := ⟨curve u, hu⟩
  let b : segmentVertices segments := ⟨curve v, hv⟩
  have uv : u < v := ut.trans tv
  have u_interval : u ∈ Icc (0 : ℝ) 1 := ⟨lower, uv.le.trans upper⟩
  have v_interval : v ∈ Icc (0 : ℝ) 1 := ⟨lower.trans uv.le, upper⟩
  have in_segment (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) : curve w ∈ s.points := by
    rw [FaceSegment.points, segment_eq_image_lineMap]
    exact ⟨w, hw, rfl⟩
  refine ⟨a, b, ⟨?_, ⟨s, hs, in_segment u u_interval, in_segment v v_interval⟩, ?_⟩, ?_⟩
  · intro same
    exact uv.ne (injective (congrArg Subtype.val same))
  · apply disjoint_left.mpr
    intro y hy vertex
    change y ∈ openSegment ℝ (curve u) (curve v) at hy
    rw [← image_openSegment ℝ curve, openSegment_eq_Ioo uv] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact disjoint_left.mp consecutive hw vertex
  · change x ∈ openSegment ℝ (curve u) (curve v)
    rw [← image_openSegment ℝ curve, openSegment_eq_Ioo uv]
    exact ⟨t, ⟨ut, tv⟩, equal⟩

/-- The graph vertices and its open straight edges have exactly the original segment trace. -/
theorem segmentGraph_trace {P : ConvexPolyhedron} (segments : Set P.FaceSegment) (finite : segments.Finite) (x : Space) :
    x ∈ ⋃ s ∈ segments, s.points ↔ x ∈ segmentVertices segments ∨
      ∃ a b : segmentVertices segments, (segmentGraph segments).Adj a b ∧
        x ∈ openSegment ℝ (a : Space) (b : Space) := by
  constructor
  · intro member
    by_cases vertex : x ∈ segmentVertices segments
    · exact Or.inl vertex
    · exact Or.inr (segmentGraph_covers_nonvertex segments finite member vertex)
  · rintro (vertex | ⟨a, b, edge, member⟩)
    · exact segmentVertices_covered segments vertex
    · exact segmentGraph_edge_covered segments edge (openSegment_subset_segment ℝ _ _ member)

end SixVertexUnfolding.ConvexPolyhedron
