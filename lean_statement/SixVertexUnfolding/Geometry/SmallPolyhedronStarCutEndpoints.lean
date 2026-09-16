import SixVertexUnfolding.Geometry.StarCutEndpoints
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRayCoordinates

/-! The star cuts are precisely the rays whose terminal cut points are
original vertices. Rays ending elsewhere remain in the retained surface.
This version uses at most six vertices and triangular/quadrilateral faces,
without a canonical graph assumption. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- Away from the source, a star-cut point has an original vertex as its terminal endpoint. -/
theorem small_cutEndpoint_original_iff_starCut (a : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : {b : frontier P.body // b ≠ a}) :
    ((small_cutEndpoint size small_faces a b).val : Space) ∈ P.vertices ↔ b.val ∈ P.starCuts a := by
  constructor
  · intro original
    let c := small_cutEndpoint size small_faces a b
    obtain ⟨F, source, target⟩ := cofacial ⟨c.val, original⟩
    obtain ⟨route, member, t, at_b⟩ := P.shortest_extension_path a b.val c.val
      (small_cutEndpoint_extension size small_faces a b)
    exact P.original_route_subset_starCuts a c.val original F source target route member ⟨t, at_b⟩
  · rintro ⟨v, segment_member⟩
    have different : (v : Space) ≠ (a : Space) := by
      intro same
      apply b.property
      apply Subtype.ext
      simpa only [same, segment_same, mem_singleton_iff] using segment_member
    obtain ⟨F, source, target⟩ := cofacial v
    let c : frontier P.body := ⟨v, F.subset_frontier target⟩
    obtain ⟨route, member, straight⟩ := P.exists_straight_geodesic a c F source target
    rw [segment_eq_image_lineMap] at segment_member
    obtain ⟨s, unit, at_b⟩ := segment_member
    let t : unitInterval := ⟨s, unit⟩
    have through : route t = b.val := Subtype.ext ((straight t).trans at_b)
    have positive : 0 < t := by
      apply lt_of_le_of_ne t.property.1
      intro zero
      have equal : (0 : unitInterval) = t := Subtype.ext zero
      exact b.property (through.symm.trans (equal ▸ congrArg Prod.fst member.2))
    have cut : c ∈ P.cutSet a := Or.inr ⟨v.property,
      fun same => different (congrArg Subtype.val same)⟩
    obtain ⟨nonzero, endpoint⟩ := small_cutEndpoint_on_route size small_faces a c cut route member t positive
    have same_input : (⟨route t, nonzero⟩ : {b : frontier P.body // b ≠ a}) = b := Subtype.ext through
    rw [same_input] at endpoint
    rw [endpoint]
    exact v.property

/-- A cut point that is not an original vertex survives the star cuts. -/
theorem small_nonvertex_cutPoint_uncut (a b : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (cut : b ∈ P.cutSet a) (nonvertex : (b : Space) ∉ P.vertices) : b ∉ P.starCuts a := by
  intro on_cut
  let c : P.cutSet a := ⟨b, cut⟩
  have original := (small_cutEndpoint_original_iff_starCut size small_faces a cofacial
    ⟨b, ne_of_mem_of_not_mem cut (P.source_not_cutSet a)⟩).mpr on_cut
  rw [small_cutEndpoint_fixes size small_faces a c] at original
  exact nonvertex original

/-- Every positive point of a ray ending at a nonvertex cut point remains uncut. -/
theorem small_nonvertex_terminal_ray_uncut (a b : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (cut : b ∈ P.cutSet a) (nonvertex : (b : Space) ∉ P.vertices)
    (route : P.BoundaryCurve) (member : route ∈ P.geodesicFiber a b)
    (t : unitInterval) (positive : 0 < t) : route t ∉ P.starCuts a := by
  obtain ⟨different, endpoint⟩ := small_cutEndpoint_on_route size small_faces a b cut route member t positive
  intro on_cut
  have original := (small_cutEndpoint_original_iff_starCut size small_faces a cofacial
    ⟨route t, different⟩).mpr on_cut
  rw [endpoint] at original
  exact nonvertex original

end SixVertexUnfolding.ConvexPolyhedron
