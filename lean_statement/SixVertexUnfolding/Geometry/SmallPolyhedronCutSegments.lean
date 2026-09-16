import SixVertexUnfolding.Geometry.SmallPolyhedronFaceVoronoi
import SixVertexUnfolding.Geometry.SmallPolyhedronEdgeVoronoi
import SixVertexUnfolding.Geometry.SmallPolyhedronCutCover
import SixVertexUnfolding.Geometry.FiniteCutSegments
import SixVertexUnfolding.Geometry.MarkedCutGraph

/-! An exact finite segment decomposition of the actual cut locus, without
a canonical graph premise. The resulting embedded graph can be subdivided
at any prescribed finite set of actual cut points. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Except at finitely many parameters, every cut point has a whole neighboring cut interval. -/
theorem small_segment_cut_crossings (a : frontier P.body) (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) (injective : Function.Injective curve)
    {l r : ℝ} (ordered : l < r) (left : curve l ∈ F.val) (right : curve r ∈ F.val) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ t ∈ Ioo l r, t ∉ E → curve t ∈ P.multipleRouteLocus a →
      ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ ∀ s ∈ J ∩ Icc l r, curve s ∈ P.multipleRouteLocus a := by
  let m := (l + r) / 2
  have middle : m ∈ Ioo l r := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have in_face := affine_interval_in_face F curve ordered.le left right
  have in_body_left := F.subset_body left
  have in_body_right := F.subset_body right
  have no_vertex {t : ℝ} (ht : t ∈ Ioo l r) : curve t ∉ P.vertices :=
    P.affine_segment_nonvertex curve injective in_body_left in_body_right ht
  rcases P.nonvertex_incident_facets (F.subset_frontier (in_face m ⟨middle.1.le, middle.2.le⟩))
    (no_vertex middle) with ⟨H, _, unique⟩ | ⟨H, G, shared, target, _⟩
  · have same : F = H := unique F (in_face m ⟨middle.1.le, middle.2.le⟩)
    subst H
    let line := (P.faceCoordinates F).comp curve
    refine ⟨lineSourceCrossings (P.sourceImages a F) line,
      lineSourceCrossings_finite _ (P.sourceImages_finite a F) line, ?_⟩
    intro t ht regular cut
    have unique_t (H : P.Face) (member : curve t ∈ H.val) : H = F := by
      exact unique H (facet_contains_affine_interval H curve in_body_left in_body_right ht member
        m ⟨middle.1.le, middle.2.le⟩)
    obtain ⟨J, openJ, tJ, persists⟩ := small_face_cut_persists_along_line size small_faces a F curve
      (in_face t ⟨ht.1.le, ht.2.le⟩) unique_t cut regular
    exact ⟨J, openJ, tJ, fun s hs => persists s hs.1 (in_face s hs.2)⟩
  · have in_H := facet_contains_affine_interval H curve in_body_left in_body_right middle target.1
    have in_G := facet_contains_affine_interval G curve in_body_left in_body_right middle target.2
    obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets H G shared
    let line := chart.left.comp curve
    refine ⟨lineSourceCrossings (chart.sourceImages a) line,
      lineSourceCrossings_finite _ (chart.sourceImages_finite a) line, ?_⟩
    intro t ht regular cut
    obtain ⟨J, openJ, tJ, persists⟩ := chart.small_cut_persists_along_line size small_faces a shared curve
      ⟨in_H t ⟨ht.1.le, ht.2.le⟩, in_G t ⟨ht.1.le, ht.2.le⟩⟩ (no_vertex ht) cut regular
    exact ⟨J, openJ, tJ, fun s hs => persists s hs.1 (in_H s hs.2)⟩

include size small_faces in
theorem small_segment_cut_frontier_finite (a : frontier P.body) (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) (injective : Function.Injective curve)
    {l r : ℝ} (ordered : l < r) (left : curve l ∈ F.val) (right : curve r ∈ F.val) :
    (frontier (Icc l r ∩ curve ⁻¹' P.cutSetInSpace a)).Finite := by
  let K := Icc l r ∩ curve ⁻¹' P.cutSetInSpace a
  have closed : IsClosed K := isClosed_Icc.inter
    ((small_cutSetInSpace_compact size small_faces a).isClosed.preimage curve.continuous_of_finiteDimensional)
  obtain ⟨E, finiteE, persists⟩ := small_segment_cut_crossings size small_faces a F curve injective ordered left right
  apply ((finiteE.insert l).insert r).subset
  intro t ht
  by_contra outside
  have not_r : t ≠ r := fun same => outside (Or.inl same)
  have not_l : t ≠ l := fun same => outside (Or.inr (Or.inl same))
  have not_E : t ∉ E := fun member => outside (Or.inr (Or.inr member))
  change t ∈ frontier K at ht
  rw [frontier, closed.closure_eq] at ht
  have interval : t ∈ Ioo l r := ⟨lt_of_le_of_ne ht.1.1.1 not_l.symm, lt_of_le_of_ne ht.1.1.2 not_r⟩
  have surface := P.cutSetInSpace_subset_boundary a ht.1.2
  let b : frontier P.body := ⟨curve t, surface⟩
  have cut := (P.mem_cutSetInSpace a b).mp ht.1.2
  have not_vertex := P.affine_segment_nonvertex curve injective (F.subset_body left) (F.subset_body right) interval
  have multiple : curve t ∈ P.multipleRouteLocus a := cut.resolve_right (fun member => not_vertex member.1)
  obtain ⟨J, openJ, tJ, whole⟩ := persists t interval not_E multiple
  have contained : J ∩ Ioo l r ⊆ K := by
    intro s hs
    have in_interval : s ∈ Icc l r := ⟨hs.2.1.le, hs.2.2.le⟩
    have surface_s := F.subset_frontier (affine_interval_in_face F curve ordered.le left right s in_interval)
    exact ⟨in_interval, (P.mem_cutSetInSpace a ⟨curve s, surface_s⟩).mpr (Or.inl (whole s ⟨hs.1, in_interval⟩))⟩
  exact ht.2 (mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset ((openJ.inter isOpen_Ioo).mem_nhds ⟨tJ, interval⟩) contained))

include size small_faces in
/-- An exact finite interval decomposition, including all boundary and vertex endpoints. -/
theorem small_segment_cut_finite_intervals (a : frontier P.body) (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) (injective : Function.Injective curve)
    {l r : ℝ} (ordered : l < r) (left : curve l ∈ F.val) (right : curve r ∈ F.val) :
    ∃ pieces : Set (ℝ × ℝ), pieces.Finite ∧
      (∀ p ∈ pieces, p.1 ≤ p.2 ∧ Icc p.1 p.2 ⊆ Icc l r ∩ curve ⁻¹' P.cutSetInSpace a) ∧
      Icc l r ∩ curve ⁻¹' P.cutSetInSpace a = ⋃ p ∈ pieces, Icc p.1 p.2 := by
  have compact : IsCompact (Icc l r ∩ curve ⁻¹' P.cutSetInSpace a) := isCompact_Icc.inter_right
    ((small_cutSetInSpace_compact size small_faces a).isClosed.preimage curve.continuous_of_finiteDimensional)
  exact compact_real_finite_intervals _ compact
    (small_segment_cut_frontier_finite size small_faces a F curve injective ordered left right)

include size small_faces in
/-- The actual cut set meets a cofacial segment in exactly finitely many cofacial closed segments. -/
theorem small_segment_cut_finite_pieces (a : frontier P.body) (s : P.FaceSegment) :
    ∃ pieces : Set P.FaceSegment, pieces.Finite ∧
      ∀ x, x ∈ s.points ∩ P.cutSetInSpace a ↔ ∃ p ∈ pieces, x ∈ p.points := by
  classical
  by_cases same : s.first = s.last
  · have singleton : s.points = {s.first} := by simp [FaceSegment.points, same]
    by_cases cut : s.first ∈ P.cutSetInSpace a
    · refine ⟨{s}, finite_singleton s, ?_⟩
      intro x
      simp only [singleton, mem_inter_iff, mem_singleton_iff, exists_eq_left]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, h ▸ cut⟩
    · refine ⟨∅, finite_empty, ?_⟩
      intro x
      simp only [singleton, mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, false_and, exists_false, iff_false]
      rintro ⟨rfl, member⟩
      exact cut member
  · let curve : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap s.first s.last
    have left : curve 0 ∈ s.face.val := by simpa only [curve, AffineMap.lineMap_apply_zero] using s.first_mem
    have right : curve 1 ∈ s.face.val := by simpa only [curve, AffineMap.lineMap_apply_one] using s.last_mem
    obtain ⟨intervals, finite_intervals, inside, exact_intervals⟩ := small_segment_cut_finite_intervals size small_faces a s.face curve (AffineMap.lineMap_injective ℝ same) (by norm_num : (0 : ℝ) < 1) left right
    let make (p : intervals) : P.FaceSegment := {
      face := s.face
      first := curve p.val.1
      last := curve p.val.2
      first_mem := affine_interval_in_face s.face curve (by norm_num : (0 : ℝ) ≤ 1) left right
        _ ((inside _ p.property).2 (left_mem_Icc.mpr (inside _ p.property).1)).1
      last_mem := affine_interval_in_face s.face curve (by norm_num : (0 : ℝ) ≤ 1) left right
        _ ((inside _ p.property).2 (right_mem_Icc.mpr (inside _ p.property).1)).1 }
    letI : Finite intervals := finite_intervals
    refine ⟨range make, finite_range make, ?_⟩
    have image_piece (p : intervals) : (make p).points = curve '' Icc p.val.1 p.val.2 := by
      rw [← segment_eq_Icc (inside _ p.property).1, image_segment]
      rfl
    have whole : s.points = curve '' Icc (0 : ℝ) 1 := by
      rw [← segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1), image_segment]
      simp only [curve, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      rfl
    intro x
    constructor
    · rintro ⟨member, cut⟩
      rw [whole] at member
      obtain ⟨t, ht, rfl⟩ := member
      have parameter : t ∈ Icc (0 : ℝ) 1 ∩ curve ⁻¹' P.cutSetInSpace a := ⟨ht, cut⟩
      rw [exact_intervals] at parameter
      obtain ⟨p, member⟩ := mem_iUnion.mp parameter
      obtain ⟨hp, interval⟩ := mem_iUnion.mp member
      refine ⟨make ⟨p, hp⟩, mem_range_self _, ?_⟩
      rw [image_piece]
      exact ⟨t, interval, rfl⟩
    · rintro ⟨_, ⟨p, rfl⟩, member⟩
      rw [image_piece] at member
      obtain ⟨t, ht, rfl⟩ := member
      have parameter := (inside _ p.property).2 ht
      exact ⟨whole ▸ ⟨t, parameter.1, rfl⟩, parameter.2⟩

include size small_faces in
/-- The cut set is exactly a finite union of closed segments in whole original facets. -/
theorem small_cutSet_finite_segments (a : frontier P.body) :
    ∃ segments : Set P.FaceSegment, segments.Finite ∧
      P.cutSetInSpace a = ⋃ s ∈ segments, s.points := by
  obtain ⟨cover, finite_cover, covers⟩ := small_cut_finite_segment_cover size small_faces a
  letI : Finite cover := finite_cover
  choose pieces finite_pieces exact_pieces using
    (fun s : cover => small_segment_cut_finite_pieces size small_faces a s.val)
  refine ⟨⋃ s : cover, pieces s, finite_iUnion finite_pieces, ?_⟩
  ext x
  constructor
  · intro cut
    obtain ⟨s, hs, on_segment⟩ := covers x cut
    obtain ⟨p, hp, on_piece⟩ := (exact_pieces ⟨s, hs⟩ x).mp ⟨on_segment, cut⟩
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨mem_iUnion.mpr ⟨⟨s, hs⟩, hp⟩, on_piece⟩⟩
  · intro member
    obtain ⟨p, member⟩ := mem_iUnion.mp member
    obtain ⟨hp, on_piece⟩ := mem_iUnion.mp member
    obtain ⟨s, hp⟩ := mem_iUnion.mp hp
    exact ((exact_pieces s x).mpr ⟨p, hp, on_piece⟩).2

include size small_faces in
/-- The actual cut set is a finite embedded graph of cofacial straight edges. -/
theorem small_exists_embedded_cut_graph (a : frontier P.body) : Nonempty (P.EmbeddedCutGraph a) := by
  obtain ⟨segments, finite, exact_segments⟩ := small_cutSet_finite_segments size small_faces a
  exact ⟨EmbeddedCutGraph.of_segments a segments finite exact_segments⟩

include size small_faces in
/-- Any finite set of actual cut points can be included among the graph's subdivision vertices. -/
theorem small_exists_cut_graph_containing (a : frontier P.body) (marks : Set Space)
    (finite_marks : marks.Finite) (marks_cut : marks ⊆ P.cutSetInSpace a) :
    ∃ K : P.EmbeddedCutGraph a, marks ⊆ K.vertices := by
  classical
  obtain ⟨segments, finite, exact_segments⟩ := small_cutSet_finite_segments size small_faces a
  letI : Finite marks := finite_marks
  have in_face (x : marks) : ∃ F : P.Face, (x : Space) ∈ F.val :=
    P.boundary_point_in_face (P.cutSetInSpace_subset_boundary a (marks_cut x.property))
  choose face member using in_face
  let point (x : marks) : P.FaceSegment := ⟨face x, x, x, member x, member x⟩
  let all := segments ∪ range point
  have finite_all : all.Finite := finite.union (finite_range point)
  have exact_all : P.cutSetInSpace a = ⋃ s ∈ all, s.points := by
    ext x
    constructor
    · intro cut
      rw [exact_segments] at cut
      obtain ⟨s, covered⟩ := mem_iUnion.mp cut
      obtain ⟨hs, member⟩ := mem_iUnion.mp covered
      exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨Or.inl hs, member⟩⟩
    · intro covered
      obtain ⟨s, hs⟩ := mem_iUnion.mp covered
      obtain ⟨hs, member⟩ := mem_iUnion.mp hs
      rcases hs with old | ⟨y, rfl⟩
      · rw [exact_segments]
        exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨old, member⟩⟩
      · have same : x = (y : Space) := by simpa only [point, FaceSegment.points, segment_same, mem_singleton_iff] using member
        exact same.symm ▸ marks_cut y.property
  refine ⟨EmbeddedCutGraph.of_segments a all finite_all exact_all, ?_⟩
  intro x hx
  exact Or.inl (Or.inl ⟨point ⟨x, hx⟩, Or.inr ⟨⟨x, hx⟩, rfl⟩, rfl⟩)

end SixVertexUnfolding.ConvexPolyhedron
