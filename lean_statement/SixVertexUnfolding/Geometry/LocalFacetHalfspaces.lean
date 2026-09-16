import SixVertexUnfolding.Geometry.NormalizedFacetPlanes
import SixVertexUnfolding.Geometry.NonvertexFacetNeighborhoods

/-! Near a surface point, only its incident facet inequalities matter.
This gives exact local planes and wedges, rather than just containment in them. -/

namespace SixVertexUnfolding.ConvexPolyhedron.NormalizedFacets

open Set

variable {P : ConvexPolyhedron} {center : Space} (facets : NormalizedFacets P center)

/-- The normalized supporting inequalities recover the original convex body. -/
theorem mem_body_iff (x : Space) :
    x ∈ P.body ↔ ∀ F : P.Face, inner ℝ (facets.normal F) (x - center) ≤ 1 := by
  have body := P.mem_body_iff_facet_inequalities facets.normal
    (fun F => 1 + inner ℝ (facets.normal F) center) facets.normal_ne_zero
    (fun F y hy => by have bound := facets.support F y hy; rw [inner_sub_right] at bound; linarith)
    (fun F => by
      rw [facets.face_eq F]
      ext y
      simp only [mem_setOf_eq, inner_sub_right]
      constructor <;> rintro ⟨hy, equal⟩ <;> exact ⟨hy, by linarith⟩) x
  rw [body]
  constructor
  · intro bounds F
    have bound := bounds F
    rw [inner_sub_right]
    linarith
  · intro bounds F
    have bound := bounds F
    rw [inner_sub_right] at bound
    linarith

/-- A facet inequality is strict at every solid point outside that facet. -/
theorem strict_of_not_mem_face (F : P.Face) {z : Space}
    (in_body : z ∈ P.body) (outside : z ∉ F.val) :
    inner ℝ (facets.normal F) (z - center) < 1 := by
  apply (facets.support F z in_body).lt_of_ne
  intro equal
  exact outside (facets.face_eq F ▸ ⟨in_body, equal⟩)

/-- All nonincident inequalities stay strict in a single open neighborhood. -/
theorem nonincident_inequalities_neighborhood {z : Space} (in_body : z ∈ P.body) :
    ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧
      ∀ x ∈ U, ∀ F : P.Face, z ∉ F.val → inner ℝ (facets.normal F) (x - center) < 1 := by
  let absent := {F : P.Face // z ∉ F.val}
  let U : Set Space := ⋂ F : absent, {x | inner ℝ (facets.normal F.val) (x - center) < 1}
  refine ⟨U, isOpen_iInter_of_finite (fun F => isOpen_lt (by fun_prop) continuous_const), ?_, ?_⟩
  · exact mem_iInter.mpr (fun F => facets.strict_of_not_mem_face F.val in_body F.property)
  · intro x hx F outside
    exact mem_iInter.mp hx ⟨F, outside⟩

/-- Locally, membership in the solid requires only the inequalities active at the center. -/
theorem local_body_iff {z : Space} (in_body : z ∈ P.body) :
    ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧
      ∀ x ∈ U, (x ∈ P.body ↔ ∀ F : P.Face, z ∈ F.val → inner ℝ (facets.normal F) (x - center) ≤ 1) := by
  obtain ⟨U, openU, zU, strict⟩ := facets.nonincident_inequalities_neighborhood in_body
  refine ⟨U, openU, zU, fun x hx => ⟨fun member F _ => facets.support F x member, ?_⟩⟩
  intro active
  apply (facets.mem_body_iff x).mpr
  intro F
  by_cases incident : z ∈ F.val
  · exact active F incident
  · exact (strict x hx F incident).le

include facets in
/-- At a point belonging to only one facet, that facet is locally its whole affine plane. -/
theorem single_face_local_plane (F : P.Face) {z : Space} (zF : z ∈ F.val)
    (unique : ∀ G : P.Face, z ∈ G.val → G = F) :
    ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧
      U ∩ F.val = U ∩ (affineSpan ℝ F.val : Set Space) := by
  obtain ⟨U, openU, zU, body⟩ := facets.local_body_iff (F.subset_body zF)
  refine ⟨U, openU, zU, ?_⟩
  ext x
  constructor
  · exact fun hx => ⟨hx.1, subset_affineSpan ℝ _ hx.2⟩
  · rintro ⟨xU, plane⟩
    have equality := facets.on_plane F plane
    have inside : x ∈ P.body := (body x xU).mpr (by
      intro G zG; rw [unique G zG]; exact equality.le)
    exact ⟨xU, facets.face_eq F ▸ ⟨inside, equality⟩⟩

/-- Along an edge interior, the first facet is exactly a half-plane near the point. -/
theorem edge_local_halfplane (F G : P.Face) (shared : P.ShareEdge F G)
    {z : Space} (hz : z ∈ F.val ∩ G.val) (not_vertex : z ∉ P.vertices) :
    ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧
      ∀ x ∈ U, (x ∈ F.val ↔ x ∈ affineSpan ℝ F.val ∧
        inner ℝ (facets.normal G) (x - center) ≤ 1) := by
  obtain ⟨U, openU, zU, body⟩ := facets.local_body_iff (F.subset_body hz.1)
  refine ⟨U, openU, zU, fun x xU => ⟨?_, ?_⟩⟩
  · intro xF
    exact ⟨subset_affineSpan ℝ _ xF, facets.support G x (F.subset_body xF)⟩
  · rintro ⟨plane, below⟩
    have equality := facets.on_plane F plane
    have inside : x ∈ P.body := (body x xU).mpr (by
      intro H zH
      rcases F.contains_edge_of_interior_point G H shared hz not_vertex zH with rfl | rfl
      exacts [equality.le, below])
    exact facets.face_eq F ▸ ⟨inside, equality⟩

end SixVertexUnfolding.ConvexPolyhedron.NormalizedFacets
