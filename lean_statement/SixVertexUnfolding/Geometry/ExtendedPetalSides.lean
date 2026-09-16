import SixVertexUnfolding.Geometry.DomeDevelopment
import SixVertexUnfolding.Geometry.FacetCornerCone
import SixVertexUnfolding.Geometry.NormalizedFacetPlanes
import SixVertexUnfolding.Geometry.HingeDeterminant
import SixVertexUnfolding.Geometry.ExtendedHinge
import SixVertexUnfolding.Geometry.ExtendedHingeSides
import SixVertexUnfolding.Geometry.PlacementRigidity

/-! Outward polygonal petals remain outward on the corresponding extended half-plane. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Dome.Development

variable {P : ConvexPolyhedron} {dome : P.Dome} (net : dome.Development)

/-- Extend outwardness to an auxiliary point in the petal plane on the solid's side of the base. -/
theorem outward_on_plane {center : Space} (facets : P.NormalizedFacets center)
    (F : P.Face) (F_side : F ≠ dome.base) (a b : P.Vertex)
    (aB : (a : Space) ∈ dome.base.val) (bB : (b : Space) ∈ dome.base.val)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) (ab : a ≠ b)
    (x : Space) (xB : x ∈ dome.base.val) (z : Space) (zF : z ∈ affineSpan ℝ F.val)
    (z_inside : inner ℝ (facets.normal dome.base) (z - center) ≤ 1) :
    OppositeHingeSides (net.place dome.base a) (net.place dome.base b)
      (net.place dome.base x) (net.place F z) := by
  obtain ⟨y, yF, yB⟩ := F.exists_vertex_not_mem_face dome.base F_side
  have ab' : (a : Space) ≠ (b : Space) := fun same => ab (Subtype.ext same)
  have triangle := P.no_three_collinear_vertices a.property b.property y.property ab'
    (fun same => yB (same ▸ aB)) (fun same => yB (same ▸ bB))
  obtain ⟨t, u, coordinates⟩ := F.plane_triangle_coordinates_of_mem_plane a b y z
    (subset_affineSpan ℝ _ aF) (subset_affineSpan ℝ _ bF) (subset_affineSpan ℝ _ yF) triangle zF
  have a_height := facets.on_face dome.base aB
  have b_height := facets.on_face dome.base bB
  have y_height : inner ℝ (facets.normal dome.base) ((y : Space) - center) < 1 := by
    apply lt_of_le_of_ne (facets.support dome.base y (F.subset_body yF))
    intro equal
    apply yB
    rw [facets.face_eq dome.base]
    exact ⟨F.subset_body yF, equal⟩
  have u_nonnegative : 0 ≤ u := by
    have measured := congrArg (fun v : Space => inner ℝ (facets.normal dome.base) v) coordinates
    simp only [inner_add_right, inner_sub_right, inner_smul_right] at measured
    rw [inner_sub_right] at a_height b_height y_height z_inside
    have zero : inner ℝ (facets.normal dome.base) (b : Space) -
        inner ℝ (facets.normal dome.base) (a : Space) = 0 := by linarith
    rw [zero, mul_zero, zero_add] at measured
    have negative : inner ℝ (facets.normal dome.base) (y : Space) -
        inner ℝ (facets.normal dome.base) (a : Space) < 0 := by linarith
    by_contra nonpositive
    have positive := mul_pos_of_neg_of_neg (lt_of_not_ge nonpositive) negative
    linarith
  have joined_a := net.joined F ⟨aB, aF⟩
  have joined_b := net.joined F ⟨bB, bF⟩
  have placed_ab : net.place dome.base a ≠ net.place dome.base b := by
    intro same
    have distance := net.rigid dome.base a aB b bB
    rw [same, dist_self] at distance
    exact ab' (dist_eq_zero.mp distance.symm)
  have mapped := congrArg (net.place F).linear coordinates
  have map_difference (v w : Space) : (net.place F).linear (v - w) = net.place F v - net.place F w :=
    (net.place F).linearMap_vsub v w
  simp only [map_add, map_smul, map_difference, ← joined_a, ← joined_b] at mapped
  have original := net.outward F F_side a ⟨⟨aB, aF⟩, a.property⟩
    b ⟨⟨bB, bF⟩, b.property⟩ ab' x xB y yF
  rw [oppositeHingeSides_iff_det _ _ _ _ placed_ab] at original ⊢
  rw [mapped, det_add_right, det_smul_right, det_smul_right, det_self, mul_zero, zero_add]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos u_nonnegative original]

/-- Outwardness may also be anchored at a virtual corner on the extended hinge. -/
theorem outward_from_virtual_corner {center : Space} (facets : P.NormalizedFacets center)
    (F : P.Face) (F_side : F ≠ dome.base) (a b : P.Vertex)
    (aB : (a : Space) ∈ dome.base.val) (bB : (b : Space) ∈ dome.base.val)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) (ab : a ≠ b)
    (o : Space) (oB : o ∈ affineSpan ℝ dome.base.val) (oF : o ∈ affineSpan ℝ F.val)
    (oa : o ≠ (a : Space)) (x : Space) (xB : x ∈ dome.base.val)
    (z : Space) (zF : z ∈ affineSpan ℝ F.val)
    (z_inside : inner ℝ (facets.normal dome.base) (z - center) ≤ 1) :
    OppositeHingeSides (net.place dome.base o) (net.place dome.base a)
      (net.place dome.base x) (net.place F z) := by
  have rigid := affine_rigid_on_span_of_distances (net.place dome.base) _ dome.base.nonempty
    (net.rigid dome.base)
  have different (v w : Space) (hv : v ∈ affineSpan ℝ dome.base.val)
      (hw : w ∈ affineSpan ℝ dome.base.val) (ne : v ≠ w) : net.place dome.base v ≠ net.place dome.base w := by
    intro same
    have distance := rigid v hv w hw
    rw [same, dist_self] at distance
    exact ne (dist_eq_zero.mp distance.symm)
  have a_plane := subset_affineSpan ℝ _ aB
  have b_plane := subset_affineSpan ℝ _ bB
  have ab' : (a : Space) ≠ (b : Space) := fun same => ab (Subtype.ext same)
  have line := dome.base.mem_extended_hinge_line F (dome.side_shares_base F F_side)
    a b ab' ⟨aB, aF⟩ ⟨bB, bF⟩ oB oF
  have placed_line : net.place dome.base o ∈
      affineSpan ℝ ({net.place dome.base a, net.place dome.base b} : Set Plane) := by
    obtain ⟨t, equal⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp line
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨t, ?_⟩
    rw [← AffineMap.apply_lineMap, equal]
  apply (oppositeHingeSides_on_same_line _ _ _ _ _ _
    (different a b a_plane b_plane ab') (different o a oB a_plane oa)
    placed_line (subset_affineSpan ℝ _ (by simp))).mpr
  exact net.outward_on_plane facets F F_side a b aB bB aF bF ab x xB z zF z_inside

end SixVertexUnfolding.ConvexPolyhedron.Dome.Development
