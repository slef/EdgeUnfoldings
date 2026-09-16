import SixVertexUnfolding.Geometry.EnlargeContact
import SixVertexUnfolding.Geometry.Edges

/-!
A one-dimensional supporting contact is a shared original edge. Enlarge it to
one facet, then enlarge it again while excluding a new vertex of the first facet.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

variable (P : ConvexPolyhedron)

theorem body_inter_contact_span (n x : Space) :
    P.body ∩ (affineSpan ℝ (P.contactSet n x) : Set Space) = P.contactSet n x := by
  have agree : Set.EqOn (innerSL ℝ n).toLinearMap.toAffineMap
      (AffineMap.const ℝ Space (inner ℝ n x)) (P.contactSet n x) := fun _ hy => hy.2
  apply Set.Subset.antisymm
  · rintro y ⟨hy, in_span⟩
    exact ⟨hy, AffineMap.eqOn_affineSpan agree in_span⟩
  · intro y hy
    exact ⟨hy.1, subset_affineSpan ℝ _ hy⟩

theorem contactSet_mono {n m x : Space}
    (support_n : P.SupportsAt n x) (support_m : P.SupportsAt m x) (point : x ∈ P.body)
    (inclusion : P.contactVertices n x ⊆ P.contactVertices m x) :
    P.contactSet n x ⊆ P.contactSet m x := by
  rw [P.contactSet_eq_convexHull n x support_n point,
    P.contactSet_eq_convexHull m x support_m point]
  exact convexHull_mono inclusion

/-- Adding contact vertices strictly increases the dimension of a supporting contact. -/
theorem contact_dimension_lt_of_strict_subset {n m x : Space}
    (support : P.SupportsAt n x) (point : x ∈ P.body)
    (larger : P.contactVertices n x ⊂ P.contactVertices m x) :
    affineDimension (P.contactVertices n x : Set Space) <
      affineDimension (P.contactVertices m x : Set Space) := by
  have inclusion : (P.contactVertices n x : Set Space) ⊆ (P.contactVertices m x : Set Space) :=
    larger.1
  apply lt_of_le_of_ne (affineDimension_mono inclusion)
  intro equal_dimensions
  have nonempty : (P.contactVertices n x : Set Space).Nonempty :=
    convexHull_nonempty_iff.mp ⟨x, P.point_mem_contact_hull n x support point⟩
  have spans := affineSpan_eq_of_subset_of_dimension_eq nonempty inclusion equal_dimensions
  have agree : Set.EqOn (innerSL ℝ n).toLinearMap.toAffineMap
      (AffineMap.const ℝ Space (inner ℝ n x)) (P.contactVertices n x : Set Space) := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  apply larger.2
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨(Finset.mem_filter.mp hv).1, AffineMap.eqOn_affineSpan agree ?_⟩
  rw [spans]
  exact subset_affineSpan ℝ _ hv

theorem contact_isFace {n x : Space} (nonzero : n ≠ 0)
    (support : P.SupportsAt n x) (point : x ∈ P.body)
    (dimension : affineDimension (P.contactVertices n x : Set Space) = 2) :
    P.IsFace (P.contactSet n x) := by
  refine ⟨?_, n, inner ℝ n x, nonzero, support, rfl⟩
  rw [P.contactSet_eq_convexHull n x support point, affineDimension_convexHull]
  exact dimension

/-- A supporting contact of dimension one is exactly the intersection of two facets. -/
theorem exists_facets_of_one_dimensional_contact (n x : Space) (nonzero : n ≠ 0)
    (support : P.SupportsAt n x) (point : x ∈ P.body)
    (dimension : affineDimension (P.contactVertices n x : Set Space) = 1) :
    ∃ F G : P.Face, P.ShareEdge F G ∧ F.val ∩ G.val = P.contactSet n x := by
  classical
  -- The first enlargement produces a facet and a new contact vertex z.
  obtain ⟨m, m_nonzero, m_support, larger⟩ :=
    P.enlarge_contact n x nonzero support point dimension.le
  have dimension_m : affineDimension (P.contactVertices m x : Set Space) = 2 := by
    have lower := P.contact_dimension_lt_of_strict_subset support point larger
    have upper := P.contact_dimension_le_two m x m_nonzero
    omega
  let F : P.Face := ⟨P.contactSet m x, P.contact_isFace m_nonzero m_support point dimension_m⟩
  have new_vertex : ∃ z, z ∈ P.contactVertices m x ∧ z ∉ P.contactVertices n x := by
    by_contra none
    push Not at none
    exact larger.2 none
  obtain ⟨z, z_in_m, z_not_n⟩ := new_vertex
  have z_vertex := (Finset.mem_filter.mp z_in_m).1
  have excluded : inner ℝ n z < inner ℝ n x := by
    apply lt_of_le_of_ne (support z (P.vertices_subset_body z_vertex))
    intro equal
    exact z_not_n (Finset.mem_filter.mpr ⟨z_vertex, equal⟩)

  -- Preserve the old edge while keeping z strictly outside the second contact plane.
  obtain ⟨k, k_nonzero, k_support, larger_k, still_excluded⟩ :=
    P.enlarge_contact_avoiding n x z support point excluded dimension.le
  have dimension_k : affineDimension (P.contactVertices k x : Set Space) = 2 := by
    have lower := P.contact_dimension_lt_of_strict_subset support point larger_k
    have upper := P.contact_dimension_le_two k x k_nonzero
    omega
  let G : P.Face := ⟨P.contactSet k x, P.contact_isFace k_nonzero k_support point dimension_k⟩
  have distinct : F ≠ G := by
    intro equal
    have z_in_F : z ∈ F.val := ⟨P.vertices_subset_body z_vertex, (Finset.mem_filter.mp z_in_m).2⟩
    have z_in_G : z ∈ G.val := equal ▸ z_in_F
    exact (ne_of_lt still_excluded) z_in_G.2
  have inclusion : P.contactSet n x ⊆ F.val ∩ G.val := fun y hy =>
    ⟨P.contactSet_mono support m_support point larger.1 hy,
      P.contactSet_mono support k_support point larger_k.1 hy⟩
  have contact_dimension : affineDimension (P.contactSet n x) = 1 := by
    rw [P.contactSet_eq_convexHull n x support point, affineDimension_convexHull, dimension]
  have intersection_dimension : affineDimension (F.val ∩ G.val) = 1 := by
    have lower := affineDimension_mono inclusion
    have upper := F.intersection_dimension_le_one G distinct
    omega
  have same_span := affineSpan_eq_of_subset_of_dimension_eq
    (show (P.contactSet n x).Nonempty from ⟨x, point, rfl⟩) inclusion
    (contact_dimension.trans intersection_dimension.symm)
  refine ⟨F, G, intersection_dimension, Set.Subset.antisymm ?_ inclusion⟩
  intro y hy
  rw [← P.body_inter_contact_span n x]
  exact ⟨F.subset_body hy.1, same_span.symm ▸ subset_affineSpan ℝ _ hy⟩

end SixVertexUnfolding.ConvexPolyhedron
