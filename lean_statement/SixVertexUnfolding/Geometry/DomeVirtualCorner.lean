import SixVertexUnfolding.Geometry.ThreeFacetPlanes
import SixVertexUnfolding.Geometry.ExtendedPetalSides
import SixVertexUnfolding.Geometry.MetricCornerCones

/-! An intersection of extended hinges supplies a separator for two whole dome petals. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Dome.Development

variable {P : ConvexPolyhedron} {dome : P.Dome} (net : dome.Development)

/-- Nonparallel petals are separated using a virtual trihedral corner outside the polygons. -/
theorem petals_nonoverlap_of_common_plane_point {center : Space} (facets : P.NormalizedFacets center)
    (F G : P.Face) (F_side : F ≠ dome.base) (G_side : G ≠ dome.base) (different : F ≠ G)
    (a a' b b' : P.Vertex) (aa' : a ≠ a') (bb' : b ≠ b')
    (aB : (a : Space) ∈ dome.base.val) (a'B : (a' : Space) ∈ dome.base.val)
    (bB : (b : Space) ∈ dome.base.val) (b'B : (b' : Space) ∈ dome.base.val)
    (aF : (a : Space) ∈ F.val) (a'F : (a' : Space) ∈ F.val)
    (bG : (b : Space) ∈ G.val) (b'G : (b' : Space) ∈ G.val)
    (aG : (a : Space) ∉ G.val) (bF : (b : Space) ∉ F.val)
    (o : Space) (oB : o ∈ affineSpan ℝ dome.base.val)
    (oF : o ∈ affineSpan ℝ F.val) (oG : o ∈ affineSpan ℝ G.val) :
    Disjoint (interior (net.place F '' F.val)) (interior (net.place G '' G.val)) := by
  obtain ⟨z, z_height, zF_height, zG_height⟩ := facets.exists_prescribed_heights dome.base F G
    F_side.symm G_side.symm different o oB oF oG 0 1 1
  have zF := (facets.mem_plane_iff F z).mpr zF_height
  have zG := (facets.mem_plane_iff G z).mpr zG_height
  have zB : z ∉ affineSpan ℝ dome.base.val := by
    intro member
    have value := facets.on_plane dome.base member
    linarith
  have z_inside : inner ℝ (facets.normal dome.base) (z - o) < 0 := by
    have origin := facets.on_plane dome.base oB
    rw [inner_sub_right] at z_height origin ⊢
    linarith
  have a_outside := G.outside_affineSpan (P.vertices_subset_body a.property) aG
  have b_outside := F.outside_affineSpan (P.vertices_subset_body b.property) bF
  have oa : o ≠ (a : Space) := fun same => a_outside (same ▸ oG)
  have ob : o ≠ (b : Space) := fun same => b_outside (same ▸ oF)
  have aB_plane := subset_affineSpan ℝ _ aB
  have bB_plane := subset_affineSpan ℝ _ bB
  have aF_plane := subset_affineSpan ℝ _ aF
  have bG_plane := subset_affineSpan ℝ _ bG
  have base_triangle := F.not_collinear_of_plane_outside o a b oF aF_plane oa b_outside
  have left_triangle := dome.base.not_collinear_of_plane_outside o a z oB aB_plane oa zB
  have right_triangle := dome.base.not_collinear_of_plane_outside o b z oB bB_plane ob zB
  have spatial : z ∉ affineSpan ℝ ({o, (a : Space), (b : Space)} : Set Space) := by
    rw [dome.base.plane_triangle_spans o a b oB aB_plane bB_plane base_triangle]
    exact zB
  have joined_oF := dome.base.joined_on_extended_hinge F (dome.side_shares_base F F_side)
    (net.place dome.base) (net.place F) (net.joined F) ⟨oB, oF⟩
  have joined_oG := dome.base.joined_on_extended_hinge G (dome.side_shares_base G G_side)
    (net.place dome.base) (net.place G) (net.joined G) ⟨oB, oG⟩
  have joined_aF := net.joined F ⟨aB, aF⟩
  have joined_bG := net.joined G ⟨bB, bG⟩
  have left_cone := F.placed_in_corner_cone (net.place F) o a z oF aF_plane zF left_triangle
    (innerSL ℝ (facets.normal dome.base)).toLinearMap (innerSL ℝ (facets.normal G)).toLinearMap
    (facets.difference_zero dome.base oB aB_plane) z_inside
    (facets.difference_zero G oG zG)
    (facets.difference_negative G oG (P.vertices_subset_body a.property) aG)
    (fun x hx => facets.difference_nonpositive dome.base oB (F.subset_body hx))
    (fun x hx => facets.difference_nonpositive G oG (F.subset_body hx))
  have right_cone := G.placed_in_corner_cone (net.place G) o b z oG bG_plane zG right_triangle
    (innerSL ℝ (facets.normal dome.base)).toLinearMap (innerSL ℝ (facets.normal F)).toLinearMap
    (facets.difference_zero dome.base oB bB_plane) z_inside
    (facets.difference_zero F oF zF)
    (facets.difference_negative F oF (P.vertices_subset_body b.property) bF)
    (fun x hx => facets.difference_nonpositive dome.base oB (G.subset_body hx))
    (fun x hx => facets.difference_nonpositive F oF (G.subset_body hx))
  rw [← joined_oF, ← joined_aF] at left_cone
  rw [← joined_oG, ← joined_bG] at right_cone
  have rigid (H : P.Face) := affine_rigid_on_span_of_distances (net.place H) H.val H.nonempty (net.rigid H)
  apply Disjoint.mono (interior_mono left_cone) (interior_mono right_cone)
  apply outward_trihedral_cones_disjoint o a b z
    (net.place dome.base o) (net.place dome.base a) (net.place dome.base b)
    (net.place F z) (net.place G z) oa ob base_triangle spatial
    (rigid dome.base o oB a aB_plane) (rigid dome.base o oB b bB_plane)
    (rigid dome.base a aB_plane b bB_plane)
  · rw [joined_oF]
    exact rigid F o oF z zF
  · rw [joined_aF]
    exact rigid F a aF_plane z zF
  · rw [joined_oG]
    exact rigid G o oG z zG
  · rw [joined_bG]
    exact rigid G b bG_plane z zG
  · exact net.outward_from_virtual_corner facets F F_side a a' aB a'B aF a'F aa'
      o oB oF oa b bB z zF (by linarith)
  · exact net.outward_from_virtual_corner facets G G_side b b' bB b'B bG b'G bb'
      o oB oG ob a aB z zG (by linarith)

end SixVertexUnfolding.ConvexPolyhedron.Dome.Development
