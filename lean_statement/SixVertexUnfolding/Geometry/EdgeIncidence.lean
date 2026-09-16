import SixVertexUnfolding.Geometry.NormalizedFacets
import SixVertexUnfolding.Geometry.Edges

/-! Every original edge belongs to exactly two whole facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron.NormalizedFacets

variable {P : ConvexPolyhedron} {center : Space} (facets : NormalizedFacets P center)

/-- Facets through a fixed nontrivial segment have normalized normals on one line. -/
theorem normals_through_pair_collinear (a b : Space) (distinct : a ≠ b)
    (F : P.Face) (a_in : a ∈ F.val) (b_in : b ∈ F.val) :
    Collinear ℝ (facets.normal '' {G : P.Face | a ∈ G.val ∧ b ∈ G.val}) := by
  let edge := b - a
  let radial := a - center
  let L := Submodule.span ℝ ({edge, radial} : Set Space)
  let normals := facets.normal '' {G : P.Face | a ∈ G.val ∧ b ∈ G.val}
  have edge_nonzero : edge ≠ 0 := sub_ne_zero.mpr distinct.symm
  have edge_height (G : P.Face) (ha : a ∈ G.val) (hb : b ∈ G.val) :
      inner ℝ (facets.normal G) edge = 0 := by
    have at_a := facets.on_face G ha
    have at_b := facets.on_face G hb
    dsimp [edge]
    simp only [inner_sub_right] at at_a at_b ⊢
    linarith
  have radial_outside : radial ∉ Submodule.span ℝ ({edge} : Set Space) := by
    intro member
    obtain ⟨t, equal⟩ := Submodule.mem_span_singleton.mp member
    have at_a := facets.on_face F a_in
    change inner ℝ (facets.normal F) radial = 1 at at_a
    rw [← equal, inner_smul_right, edge_height F a_in b_in, mul_zero] at at_a
    norm_num at at_a
  have strictly_larger : Submodule.span ℝ ({edge} : Set Space) < L := by
    apply lt_of_le_of_ne (Submodule.span_mono (by intro x hx; exact Or.inl hx))
    intro same
    apply radial_outside
    rw [same]
    exact Submodule.subset_span (Or.inr rfl)
  have dimension_lower := Submodule.finrank_lt_finrank_of_lt strictly_larger
  rw [finrank_span_singleton edge_nonzero] at dimension_lower
  have dimensions := L.finrank_add_finrank_orthogonal
  have ambient : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [ambient] at dimensions
  have equal_edge (q : Space) (hq : q ∈ normals) : inner ℝ edge q = 0 := by
    obtain ⟨G, ⟨ha, hb⟩, rfl⟩ := hq
    rw [real_inner_comm]
    exact edge_height G ha hb
  have equal_radial (q : Space) (hq : q ∈ normals) : inner ℝ radial q = 1 := by
    obtain ⟨G, ⟨ha, _⟩, rfl⟩ := hq
    rw [real_inner_comm]
    exact facets.on_face G ha
  have zero_on_span (u : Space) (level : ℝ)
      (equal : ∀ q ∈ normals, inner ℝ u q = level) {d : Space}
      (hd : d ∈ vectorSpan ℝ normals) : inner ℝ u d = 0 := by
    have agree : Set.EqOn (innerSL ℝ u).toLinearMap.toAffineMap
        (AffineMap.const ℝ Space level) normals := equal
    simpa using AffineMap.linear_eqOn_vectorSpan agree hd
  have inclusion : vectorSpan ℝ normals ≤ Lᗮ := by
    intro d hd
    apply (L.mem_orthogonal d).mpr
    intro x hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
    simp only [inner_add_left, real_inner_smul_left,
      zero_on_span edge 0 equal_edge hd, zero_on_span radial 1 equal_radial hd,
      mul_zero, add_zero]
  apply collinear_iff_finrank_le_one.mpr
  have upper := Submodule.finrank_mono inclusion
  change Module.finrank ℝ (vectorSpan ℝ normals) ≤ 1
  omega

end SixVertexUnfolding.ConvexPolyhedron.NormalizedFacets

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F G : P.Face)

/-- The only facets containing a shared original edge are its two defining facets. -/
theorem facets_containing_shared_edge (shared : P.ShareEdge F G) (H : P.Face)
    (contains : F.val ∩ G.val ⊆ H.val) : H = F ∨ H = G := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨a, _, b, _, distinct, edge_eq⟩ := F.shared_edge_endpoints G shared
  have a_shared : a ∈ F.val ∩ G.val := by rw [edge_eq]; exact left_mem_segment ℝ a b
  have b_shared : b ∈ F.val ∩ G.val := by rw [edge_eq]; exact right_mem_segment ℝ a b
  by_contra neither
  push Not at neither
  have fg : F ≠ G := by
    intro same
    subst G
    exact F.shareEdge_irrefl shared
  apply facets.no_three_collinear F G H fg neither.1.symm neither.2.symm
  apply (facets.normals_through_pair_collinear a b distinct F a_shared.1 b_shared.1).subset
  intro q hq
  rcases hq with hq | hq | hq
  · exact ⟨F, ⟨a_shared.1, b_shared.1⟩, hq.symm⟩
  · exact ⟨G, ⟨a_shared.2, b_shared.2⟩, hq.symm⟩
  · exact ⟨H, ⟨contains a_shared, contains b_shared⟩, hq.symm⟩

/-- Exactly two facets contain each shared original edge. -/
theorem two_incident_facets (shared : P.ShareEdge F G) :
    Nat.card {H : P.Face | F.val ∩ G.val ⊆ H.val} = 2 := by
  have distinct : F ≠ G := by
    intro same
    subst G
    exact F.shareEdge_irrefl shared
  have only_two : {H : P.Face | F.val ∩ G.val ⊆ H.val} = {F, G} := by
    ext H
    constructor
    · exact F.facets_containing_shared_edge G shared H
    · rintro (rfl | rfl)
      exacts [Set.inter_subset_left, Set.inter_subset_right]
  change {H : P.Face | F.val ∩ G.val ⊆ H.val}.ncard = 2
  rw [only_two]
  exact Set.ncard_pair distinct

end SixVertexUnfolding.ConvexPolyhedron.Face
