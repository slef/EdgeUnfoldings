import SixVertexUnfolding.Geometry.SegmentCutCrossings
import SixVertexUnfolding.Geometry.CompactRealIntervals
import SixVertexUnfolding.Geometry.CutSetInSpace

/-! The actual compact cut set meets every nondegenerate cofacial
straight segment in exactly finitely many closed parameter intervals. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem segment_cut_frontier_finite (a : frontier P.body) (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) (injective : Function.Injective curve)
    {l r : ℝ} (ordered : l < r) (left : curve l ∈ F.val) (right : curve r ∈ F.val) :
    (frontier (Icc l r ∩ curve ⁻¹' P.cutSetInSpace a)).Finite := by
  let K := Icc l r ∩ curve ⁻¹' P.cutSetInSpace a
  have closed : IsClosed K := isClosed_Icc.inter
    ((graph.cutSetInSpace_compact small_faces a).isClosed.preimage curve.continuous_of_finiteDimensional)
  obtain ⟨E, finiteE, persists⟩ := graph.segment_cut_crossings small_faces a F curve injective ordered left right
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

include graph small_faces in
/-- An exact finite interval decomposition, including all boundary and vertex endpoints. -/
theorem segment_cut_finite_intervals (a : frontier P.body) (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) (injective : Function.Injective curve)
    {l r : ℝ} (ordered : l < r) (left : curve l ∈ F.val) (right : curve r ∈ F.val) :
    ∃ pieces : Set (ℝ × ℝ), pieces.Finite ∧
      (∀ p ∈ pieces, p.1 ≤ p.2 ∧ Icc p.1 p.2 ⊆ Icc l r ∩ curve ⁻¹' P.cutSetInSpace a) ∧
      Icc l r ∩ curve ⁻¹' P.cutSetInSpace a = ⋃ p ∈ pieces, Icc p.1 p.2 := by
  have compact : IsCompact (Icc l r ∩ curve ⁻¹' P.cutSetInSpace a) := isCompact_Icc.inter_right
    ((graph.cutSetInSpace_compact small_faces a).isClosed.preimage curve.continuous_of_finiteDimensional)
  exact compact_real_finite_intervals _ compact
    (graph.segment_cut_frontier_finite small_faces a F curve injective ordered left right)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
