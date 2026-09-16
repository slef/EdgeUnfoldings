import SixVertexUnfolding.Geometry.Edges

/-! The common line of two neighboring facet planes is exactly the extension of their original hinge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F G : P.Face)

/-- A third point outside a facet plane cannot be collinear with two distinct points in it. -/
theorem not_collinear_of_plane_outside (o a b : Space)
    (ho : o ∈ affineSpan ℝ F.val) (ha : a ∈ affineSpan ℝ F.val) (oa : o ≠ a)
    (outside : b ∉ affineSpan ℝ F.val) : ¬ Collinear ℝ ({o, a, b} : Set Space) := by
  intro collinear
  apply outside
  have in_line := collinear.mem_affineSpan_of_mem_of_ne (by simp : o ∈ ({o, a, b} : Set Space))
    (by simp : a ∈ ({o, a, b} : Set Space)) (by simp : b ∈ ({o, a, b} : Set Space)) oa
  apply (affineSpan_le_of_subset_coe (show ({o, a} : Set Space) ⊆ affineSpan ℝ F.val from ?_)) in_line
  rintro x (rfl | rfl)
  exacts [ho, ha]

/-- Extending two neighboring facets introduces only the line extending their shared edge. -/
theorem plane_intersection_eq_hinge_span (shared : P.ShareEdge F G) :
    affineSpan ℝ F.val ⊓ affineSpan ℝ G.val = affineSpan ℝ (F.val ∩ G.val) := by
  let common := affineSpan ℝ F.val ⊓ affineSpan ℝ G.val
  have different : F ≠ G := by rintro rfl; exact F.shareEdge_irrefl shared
  have edge_nonempty : (F.val ∩ G.val).Nonempty :=
    nonempty_of_affineDimension_pos (by rw [shared]; norm_num)
  have common_nonempty : (common : Set Space).Nonempty := by
    obtain ⟨x, hx⟩ := edge_nonempty
    exact ⟨x, subset_affineSpan ℝ _ hx.1, subset_affineSpan ℝ _ hx.2⟩
  have inclusion : affineSpan ℝ (F.val ∩ G.val) ≤ common := by
    apply affineSpan_le_of_subset_coe
    exact fun x hx => ⟨subset_affineSpan ℝ _ hx.1, subset_affineSpan ℝ _ hx.2⟩
  have left_le : common ≤ affineSpan ℝ F.val := inf_le_left
  have right_le : common ≤ affineSpan ℝ G.val := inf_le_right
  have dimF : Module.finrank ℝ (affineSpan ℝ F.val).direction = 2 := F.property.1
  have dimG : Module.finrank ℝ (affineSpan ℝ G.val).direction = 2 := G.property.1
  have edge_dimension : Module.finrank ℝ (affineSpan ℝ (F.val ∩ G.val)).direction = 1 := shared
  have lower := Submodule.finrank_mono (AffineSubspace.direction_le inclusion)
  have upper := Submodule.finrank_mono (AffineSubspace.direction_le left_le)
  have dimension : Module.finrank ℝ common.direction = 1 := by
    by_contra not_one
    have two : Module.finrank ℝ common.direction = 2 := by omega
    have left_eq := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
      (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le left_le) (two.trans dimF.symm))
      common_nonempty left_le
    have right_eq := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
      (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le right_le) (two.trans dimG.symm))
      common_nonempty right_le
    exact different (F.eq_of_affineSpan_eq G (left_eq.symm.trans right_eq))
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le inclusion) (edge_dimension.trans dimension.symm))
    (edge_nonempty.affineSpan ℝ) inclusion).symm

/-- Agreement along the original hinge extends to every point common to the two facet planes. -/
theorem joined_on_extended_hinge (shared : P.ShareEdge F G)
    (left right : Space →ᵃ[ℝ] Plane) (joined : Set.EqOn left right (F.val ∩ G.val)) :
    Set.EqOn left right ((affineSpan ℝ F.val : Set Space) ∩ (affineSpan ℝ G.val : Set Space)) := by
  intro x hx
  apply AffineMap.eqOn_affineSpan joined
  rw [← F.plane_intersection_eq_hinge_span G shared]
  exact hx

/-- Any two distinct hinge points describe the whole common line of the extended facet planes. -/
theorem mem_extended_hinge_line (shared : P.ShareEdge F G) (a b : Space) (ab : a ≠ b)
    (ha : a ∈ F.val ∩ G.val) (hb : b ∈ F.val ∩ G.val) {o : Space}
    (hoF : o ∈ affineSpan ℝ F.val) (hoG : o ∈ affineSpan ℝ G.val) :
    o ∈ affineSpan ℝ ({a, b} : Set Space) := by
  have collinear : Collinear ℝ (F.val ∩ G.val) := by
    apply collinear_iff_finrank_le_one.mpr
    have dimension : Module.finrank ℝ (affineSpan ℝ (F.val ∩ G.val)).direction = 1 := shared
    rw [direction_affineSpan] at dimension
    omega
  rw [collinear.affineSpan_eq_of_ne ha hb ab, ← F.plane_intersection_eq_hinge_span G shared]
  exact ⟨hoF, hoG⟩

end SixVertexUnfolding.ConvexPolyhedron.Face
