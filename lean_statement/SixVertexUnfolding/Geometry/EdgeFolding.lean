import SixVertexUnfolding.Geometry.FoldedPlane
import SixVertexUnfolding.Geometry.HingeHalfplanes
import SixVertexUnfolding.Geometry.FacetPlaneInverse
import SixVertexUnfolding.Geometry.PolygonPetal

/-! Construct the two rigid half-planes that model a neighborhood of an
original edge. All placements, inverse maps, and side choices are supplied. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- An outward development and its inverse folding, with the exact support-side tests. -/
structure EdgeFolding {P : ConvexPolyhedron} {center : Space}
    (facets : P.NormalizedFacets center) (F G : P.Face) where
  fold : FoldedPlane
  left : Space →ᵃ[ℝ] Plane
  right : Space →ᵃ[ℝ] Plane
  first_plane : ∀ z, fold.first z ∈ affineSpan ℝ F.val
  second_plane : ∀ z, fold.second z ∈ affineSpan ℝ G.val
  left_inverse : ∀ z, left (fold.first z) = z
  right_inverse : ∀ z, right (fold.second z) = z
  first_inverse : ∀ x ∈ affineSpan ℝ F.val, fold.first (left x) = x
  second_inverse : ∀ x ∈ affineSpan ℝ G.val, fold.second (right x) = x
  joined : Set.EqOn left right (F.val ∩ G.val)
  left_halfplane : ∀ x ∈ affineSpan ℝ F.val,
    0 ≤ fold.height (left x) ↔ inner ℝ (facets.normal G) (x - center) ≤ 1
  right_halfplane : ∀ x ∈ affineSpan ℝ G.val,
    fold.height (right x) ≤ 0 ↔ inner ℝ (facets.normal F) (x - center) ≤ 1

/-- Every original edge has an outward folding of its two extended facet planes. -/
theorem exists_edge_folding {P : ConvexPolyhedron} {center : Space}
    (facets : P.NormalizedFacets center) (F G : P.Face) (shared : P.ShareEdge F G) :
    Nonempty (EdgeFolding facets F G) := by
  have different : F ≠ G := by rintro rfl; exact F.shareEdge_irrefl shared
  obtain ⟨p, p_vertex, q, q_vertex, pq, edge⟩ := F.shared_edge_endpoints G shared
  have hp : p ∈ F.val ∩ G.val := edge ▸ left_mem_segment ℝ p q
  have hq : q ∈ F.val ∩ G.val := edge ▸ right_mem_segment ℝ p q
  obtain ⟨c, cF, cG⟩ := F.exists_vertex_not_mem_face G different
  obtain ⟨d, dG, dF⟩ := G.exists_vertex_not_mem_face F different.symm
  have pc : p ≠ (c : Space) := fun same => cG (same ▸ hp.2)
  have qc : q ≠ (c : Space) := fun same => cG (same ▸ hq.2)
  have pd : p ≠ (d : Space) := fun same => dF (same ▸ hp.1)
  have qd : q ≠ (d : Space) := fun same => dF (same ▸ hq.1)
  have p_c_q := P.no_three_collinear_vertices p_vertex q_vertex c.property pq pc qc
  have p_d_q := P.no_three_collinear_vertices p_vertex q_vertex d.property pq pd qd
  obtain ⟨left, left_rigid⟩ := F.exists_rigid_placement
  obtain ⟨right, right_rigid, joined, _, _, outward⟩ := F.exists_polygon_petal G shared left left_rigid
  have at_p := joined hp
  have at_q := joined hq
  have placed_pq : left p ≠ left q := by
    intro same
    exact pq (dist_eq_zero.mp (by simpa [same] using (left_rigid p hp.1 q hq.1).symm))
  have first_triangle := P.placed_triangle_noncollinear ⟨p, p_vertex⟩ ⟨q, q_vertex⟩ c
    (fun same => pq (congrArg Subtype.val same)) (fun same => pc (congrArg Subtype.val same))
    (fun same => qc (congrArg Subtype.val same)) (left p) (left q) (left c)
    (left_rigid p hp.1 q hq.1) (left_rigid p hp.1 c cF) (left_rigid q hq.1 c cF)
  have second_triangle := P.placed_triangle_noncollinear ⟨p, p_vertex⟩ ⟨q, q_vertex⟩ d
    (fun same => pq (congrArg Subtype.val same)) (fun same => pd (congrArg Subtype.val same))
    (fun same => qd (congrArg Subtype.val same)) (right p) (right q) (right d)
    (right_rigid p hp.2 q hq.2) (right_rigid p hp.2 d dG) (right_rigid q hq.2 d dG)
  have first_transverse := hingeSideVector_ne_zero _ _ _ first_triangle
  have second_transverse := hingeSideVector_ne_zero _ _ _ second_triangle
  rw [← at_p, ← at_q] at second_transverse
  obtain ⟨factor, negative, height_factor⟩ := opposite_hinge_height_factor
    (left p) (left q) (left c) (right d) placed_pq first_transverse second_transverse
    (outward p ⟨hp, p_vertex⟩ q ⟨hq, q_vertex⟩ pq c cF d dG)
  obtain ⟨first, first_plane, left_inverse, first_inverse, first_rigid⟩ := F.exists_rigid_plane_inverse left left_rigid
  obtain ⟨second, second_plane, right_inverse, second_inverse, second_rigid⟩ := G.exists_rigid_plane_inverse right right_rigid
  let height : Plane →ᵃ[ℝ] ℝ :=
    (innerSL ℝ (hingeSideVector (left p) (left q) (left c))).toLinearMap.toAffineMap.comp
      (AffineEquiv.vaddConst ℝ (-left p)).toAffineMap
  have height_value (z : Plane) : height z = inner ℝ (hingeSideVector (left p) (left q) (left c)) (z - left p) := by
    simp [height, sub_eq_add_neg]
  have crease_agreement : ∀ z, height z = 0 → first z = second z := by
    intro z zero
    have line : z ∈ affineSpan ℝ ({left p, left q} : Set Plane) :=
      (hinge_height_zero_iff_line _ _ _ _ placed_pq first_transverse).mp ((height_value z).symm.trans zero)
    apply AffineMap.eqOn_affineSpan (s := {left p, left q}) _ line
    rintro w (rfl | rfl)
    · rw [first_inverse p (subset_affineSpan ℝ _ hp.1), at_p,
        second_inverse p (subset_affineSpan ℝ _ hp.2)]
    · rw [first_inverse q (subset_affineSpan ℝ _ hq.1), at_q,
        second_inverse q (subset_affineSpan ℝ _ hq.2)]
  let fold : FoldedPlane := ⟨height, first, second, first_rigid, second_rigid, crease_agreement⟩
  refine ⟨⟨fold, left, right, first_plane, second_plane, left_inverse, right_inverse,
    first_inverse, second_inverse, joined, ?_, ?_⟩⟩
  · intro x hx
    change 0 ≤ height (left x) ↔ _
    rw [height_value]
    exact (F.support_iff_hinge_height facets G p q c hp.1 hq.1 cF hp.2 hq.2 cG p_c_q
      left placed_pq first_transverse x hx).symm
  · intro x hx
    have comparison := G.support_iff_hinge_height facets F p q d hp.2 hq.2 dG hp.1 hq.1 dF p_d_q
      right (by rwa [← at_p, ← at_q]) (by rwa [← at_p, ← at_q]) x hx
    rw [← at_p, ← at_q, height_factor] at comparison
    change height (right x) ≤ 0 ↔ _
    rw [height_value]
    constructor
    · intro nonpositive
      exact comparison.mpr (mul_nonneg_of_nonpos_of_nonpos negative.le nonpositive)
    · intro inside
      have nonnegative := comparison.mp inside
      nlinarith

end SixVertexUnfolding.ConvexPolyhedron
