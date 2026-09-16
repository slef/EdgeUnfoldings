import SixVertexUnfolding.Geometry.BipyramidVertices
import SixVertexUnfolding.Geometry.TriangularFacets
import SixVertexUnfolding.Geometry.EdgeFacePairs

/-!
The six triangular facets are derived from the original edge incidences.
The pole-to-equator edges force all three triangles on each side.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- A triangular facet through a pole and an equator vertex has another equator vertex. -/
theorem facet_through_pole_edge
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (i : Fin 3) (F : P.Face)
    (pole_in : (B.poleVertex upper : Space) ∈ F.val)
    (equator_in : (B.equatorVertex i : Space) ∈ F.val) :
    ∃ j : Fin 3, j ≠ i ∧ F.val ∩ (P.vertices : Set Space) =
      {(B.poleVertex upper : Space), (B.equatorVertex i : Space), (B.equatorVertex j : Space)} := by
  obtain ⟨v, vp, vi, vertices⟩ := F.exists_third_vertex (triangles F)
    (B.poleVertex upper) (B.equatorVertex i) (B.pole_ne_equator upper i) pole_in equator_in
  have vF : (v : Space) ∈ F.val := by
    have member : (v : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
    exact member.1
  rcases B.vertex_cases_from_pole upper v with at_pole | at_opposite | ⟨j, at_equator⟩
  · exact False.elim (vp at_pole)
  · have edge := F.adjacent_of_triangle (triangles F) (B.poleVertex upper) v vp.symm pole_in vF
    rw [at_opposite] at edge
    exact False.elim (B.pole_opposite_not_adjacent upper edge)
  · refine ⟨j, ?_, ?_⟩
    · intro same
      exact vi (at_equator.trans (congrArg B.equatorVertex same))
    · simpa only [at_equator] using vertices

/-- Each pole and each pair of different equator vertices form an original facet. -/
theorem exists_pole_facet
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (i j : Fin 3) (different : i ≠ j) :
    ∃ F : P.Face, F.val ∩ (P.vertices : Set Space) =
      {(B.poleVertex upper : Space), (B.equatorVertex i : Space), (B.equatorVertex j : Space)} := by
  obtain ⟨F, G, distinct, poleF, iF, poleG, iG, _⟩ := P.edge_incident_faces
    (B.poleVertex upper) (B.equatorVertex i) (B.pole_equator_adjacent upper i)
  obtain ⟨k, ki, verticesF⟩ := B.facet_through_pole_edge triangles upper i F poleF iF
  obtain ⟨l, li, verticesG⟩ := B.facet_through_pole_edge triangles upper i G poleG iG
  have kl : k ≠ l := by
    intro same
    apply distinct
    apply F.eq_of_same_vertices G
    rw [verticesF, verticesG, same]
  have choices : j = k ∨ j = l := by omega
  rcases choices with same | same
  · exact ⟨F, by simpa only [same] using verticesF⟩
  · exact ⟨G, by simpa only [same] using verticesG⟩

/-- Any facet containing a pole is one of the three triangles incident to that pole. -/
theorem facet_at_pole
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (F : P.Face) (pole_in : (B.poleVertex upper : Space) ∈ F.val) :
    ∃ i j : Fin 3, i ≠ j ∧ F.val ∩ (P.vertices : Set Space) =
      {(B.poleVertex upper : Space), (B.equatorVertex i : Space), (B.equatorVertex j : Space)} := by
  have second : ∃ v : P.Vertex, (v : Space) ∈ F.val ∧ v ≠ B.poleVertex upper := by
    by_contra none
    push Not at none
    have inclusion : F.val ∩ (P.vertices : Set Space) ⊆ {(B.poleVertex upper : Space)} := by
      rintro x ⟨xF, vertex⟩
      exact congrArg Subtype.val (none ⟨x, vertex⟩ xF)
    have count := Set.ncard_le_ncard inclusion
    rw [triangles F, Set.ncard_singleton] at count
    omega
  obtain ⟨v, vF, vp⟩ := second
  rcases B.vertex_cases_from_pole upper v with at_pole | at_opposite | ⟨i, at_equator⟩
  · exact False.elim (vp at_pole)
  · have edge := F.adjacent_of_triangle (triangles F) (B.poleVertex upper) v vp.symm pole_in vF
    rw [at_opposite] at edge
    exact False.elim (B.pole_opposite_not_adjacent upper edge)
  · have iF : (B.equatorVertex i : Space) ∈ F.val := at_equator ▸ vF
    obtain ⟨j, ji, vertices⟩ := B.facet_through_pole_edge triangles upper i F pole_in iF
    exact ⟨i, j, ji.symm, vertices⟩

/-- There is no seventh facet consisting only of the equator triangle. -/
theorem every_facet_contains_pole
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) (F : P.Face) :
    (B.top : Space) ∈ F.val ∨ (B.bottom : Space) ∈ F.val := by
  by_contra no_pole
  push Not at no_pole
  let vertices : Set P.Vertex := {v | (v : Space) ∈ F.val}
  have count : vertices.ncard = 3 := by
    have image : Subtype.val '' vertices = F.val ∩ (P.vertices : Set Space) := by
      ext x
      constructor
      · rintro ⟨v, vF, rfl⟩
        exact ⟨vF, v.property⟩
      · rintro ⟨xF, vertex⟩
        exact ⟨⟨x, vertex⟩, xF, rfl⟩
    rw [← Set.ncard_image_of_injective vertices Subtype.val_injective, image]
    exact triangles F
  have inclusion : vertices ⊆ Set.range B.equatorVertex := by
    intro v vF
    rcases B.vertex_cases v with top | bottom | ⟨i, equal⟩
    · exact False.elim (no_pole.1 (top ▸ vF))
    · exact False.elim (no_pole.2 (bottom ▸ vF))
    · exact ⟨i, equal.symm⟩
  have all_equator : vertices = Set.range B.equatorVertex :=
    Set.eq_of_subset_of_ncard_le inclusion (by
      rw [Set.ncard_range_of_injective B.equator_injective, count]
      simp) (Set.finite_range _)
  have at_i (i : Fin 3) : (B.equatorVertex i : Space) ∈ F.val :=
    (show B.equatorVertex i ∈ vertices from all_equator.symm ▸ Set.mem_range_self i)
  obtain ⟨topF, top_vertices⟩ := B.exists_pole_facet triangles true 0 1 (by decide)
  obtain ⟨bottomF, bottom_vertices⟩ := B.exists_pole_facet triangles false 0 1 (by decide)
  have top_in : (B.top : Space) ∈ topF.val := by
    have member : (B.top : Space) ∈ topF.val ∩ (P.vertices : Set Space) := by
      rw [top_vertices]
      exact Or.inl rfl
    exact member.1
  have bottom_in : (B.bottom : Space) ∈ bottomF.val := by
    have member : (B.bottom : Space) ∈ bottomF.val ∩ (P.vertices : Set Space) := by
      rw [bottom_vertices]
      exact Or.inl rfl
    exact member.1
  have edge := B.equator_adjacent 0 1 (by decide)
  obtain ⟨H, K, _, _, _, _, _, only_two⟩ := P.edge_incident_faces _ _ edge
  have top_pair := only_two topF
    (by
      have h : (B.equatorVertex 0 : Space) ∈ topF.val ∩ (P.vertices : Set Space) := by rw [top_vertices]; simp
      exact h.1)
    (by
      have h : (B.equatorVertex 1 : Space) ∈ topF.val ∩ (P.vertices : Set Space) := by rw [top_vertices]; simp
      exact h.1)
  have bottom_pair := only_two bottomF
    (by
      have h : (B.equatorVertex 0 : Space) ∈ bottomF.val ∩ (P.vertices : Set Space) := by rw [bottom_vertices]; simp
      exact h.1)
    (by
      have h : (B.equatorVertex 1 : Space) ∈ bottomF.val ∩ (P.vertices : Set Space) := by rw [bottom_vertices]; simp
      exact h.1)
  have F_pair := only_two F (at_i 0) (at_i 1)
  have top_bottom : topF ≠ bottomF := by
    intro same
    have top_in_bottom : (B.top : Space) ∈ bottomF.val ∩ (P.vertices : Set Space) := ⟨same ▸ top_in, B.top.property⟩
    rw [bottom_vertices] at top_in_bottom
    rcases top_in_bottom with equal | equal | equal
    · exact B.distinct_poles (Subtype.ext equal)
    · exact (B.equator_ne_top 0) (Subtype.ext equal.symm)
    · exact (B.equator_ne_top 1) (Subtype.ext equal.symm)
  have F_top : F ≠ topF := fun same => no_pole.1 (same ▸ top_in)
  have F_bottom : F ≠ bottomF := fun same => no_pole.2 (same ▸ bottom_in)
  rcases top_pair with topH | topK <;> rcases bottom_pair with bottomH | bottomK <;>
    rcases F_pair with FH | FK <;> grind

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
