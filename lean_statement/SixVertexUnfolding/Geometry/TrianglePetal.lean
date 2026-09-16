import SixVertexUnfolding.Geometry.FacetHingeSides
import SixVertexUnfolding.Geometry.TriangleNondegeneracy
import SixVertexUnfolding.Geometry.TriangleStrictComparison
import SixVertexUnfolding.Geometry.OutwardTriangle

/-!
Unfold an original triangular facet outward from a neighboring polygonal base.
No pyramid assumption is needed: this also supplies individual bipyramid petals.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

/-- An outward triangle is disjoint from the whole base and strictly farther at missing base vertices. -/
theorem exists_triangle_petal {P : ConvexPolyhedron} (base F : P.Face)
    (a b apex : P.Vertex) (ab : a ≠ b)
    (aB : (a : Space) ∈ base.val) (bB : (b : Space) ∈ base.val)
    (vertices : F.val ∩ (P.vertices : Set Space) = {(a : Space), (b : Space), (apex : Space)})
    (apex_outside : (apex : Space) ∉ base.val)
    (left : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ base.val, ∀ y ∈ base.val, dist (left x) (left y) = dist x y) :
    ∃ right : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ F.val, ∀ y ∈ F.val, dist (right x) (right y) = dist x y) ∧
      (∀ x : P.Vertex, (x : Space) ∈ F.val → (x : Space) ∈ base.val → right x = left x) ∧
      Disjoint (interior (left '' base.val)) (interior (right '' F.val)) ∧
      (∀ x : P.Vertex, (x : Space) ∈ base.val → (x : Space) ∉ F.val →
        dist (x : Space) apex < dist (left x) (right apex)) := by
  have aF : (a : Space) ∈ F.val := by
    have : (a : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
    exact this.1
  have bF : (b : Space) ∈ F.val := by
    have : (b : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
    exact this.1
  have apexF : (apex : Space) ∈ F.val := by
    have member : (apex : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
    exact member.1
  have side : F ≠ base := by
    intro same
    exact apex_outside (same ▸ apexF)
  have third : ∃ c : P.Vertex, (c : Space) ∈ base.val ∧ (c : Space) ∉ F.val := by
    by_contra none
    push Not at none
    apply side
    apply Eq.symm
    apply base.eq_of_subset F
    rw [base.eq_convexHull_vertices]
    apply convexHull_min _ F.convex
    rintro x ⟨xB, vertex⟩
    exact none ⟨x, vertex⟩ xB
  obtain ⟨c, cB, cF⟩ := third
  have ac : a ≠ c := fun same => cF (same ▸ aF)
  have bc : b ≠ c := fun same => cF (same ▸ bF)
  have source_triangle := P.no_three_collinear_vertices a.property b.property c.property
    (fun same => ab (Subtype.ext same)) (fun same => ac (Subtype.ext same))
    (fun same => bc (Subtype.ext same))
  have edge_length := left_rigid a aB b bB
  have placed_distinct : left a ≠ left b := by
    intro same
    have equal : (a : Space) = (b : Space) := dist_eq_zero.mp (by simpa [same] using edge_length.symm)
    exact ab (Subtype.ext equal)
  obtain ⟨right, right_rigid, at_a, at_b, outward⟩ := F.exists_outward_placement
    a b c apex aF bF left edge_length placed_distinct
  have same_side (x : Space) (xB : x ∈ base.val) :
      ∃ u : ℝ, 0 ≤ u ∧ hingeSideVector (left a) (left b) (left x) =
        u • hingeSideVector (left a) (left b) (left c) :=
    base.placed_hinge_side F left a b c x aB bB cB xB aF bF cF source_triangle placed_distinct
  have all_outward (x : Space) (xB : x ∈ base.val) :
      OppositeHingeSides (left a) (left b) (left x) (right apex) := by
    obtain ⟨u, nonnegative, equal⟩ := same_side x xB
    change inner ℝ (hingeSideVector (left a) (left b) (left x))
      (hingeSideVector (left a) (left b) (right apex)) ≤ 0
    rw [equal, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos nonnegative outward
  refine ⟨right, right_rigid, ?_, ?_, ?_⟩
  · intro x xF xB
    have member : (x : Space) ∈ ({(a : Space), (b : Space), (apex : Space)} : Set Space) :=
      vertices ▸ ⟨xF, x.property⟩
    have neither_apex : (x : Space) ≠ (apex : Space) := fun same => apex_outside (same ▸ xB)
    have pair : (x : Space) = (a : Space) ∨ (x : Space) = (b : Space) := by
      rcases member with at_a | at_b | at_apex
      exacts [Or.inl at_a, Or.inr at_b, False.elim (neither_apex at_apex)]
    rcases pair with equal | equal
    · change right (x : Space) = left (x : Space)
      rw [equal, at_a]
    · change right (x : Space) = left (x : Space)
      rw [equal, at_b]
  · let n := hingeSideVector (left a) (left b) (left c)
    have placed_triangle := P.placed_triangle_noncollinear a b c ab ac bc
      (left a) (left b) (left c) edge_length (left_rigid a aB c cB) (left_rigid b bB c cB)
    have nonzero : n ≠ 0 := hingeSideVector_ne_zero (left a) (left b) (left c) placed_triangle
    have base_bound (x : Space) (xB : x ∈ base.val) : inner ℝ n (left a) ≤ inner ℝ n (left x) := by
      obtain ⟨u, nonnegative, equal⟩ := same_side x xB
      have height : 0 ≤ inner ℝ n (left x - left a) := by
        rw [hingeSideVector_inner (left a) (left b) (left c) (left x) placed_distinct,
          equal, inner_smul_right]
        exact mul_nonneg nonnegative real_inner_self_nonneg
      simpa only [inner_sub_right, sub_nonneg] using height
    have edge_height : inner ℝ n (left b) = inner ℝ n (left a) := by
      have zero : inner ℝ n (left b - left a) = 0 := by
        rw [hingeSideVector_inner (left a) (left b) (left c) (left b) placed_distinct,
          hingeSideVector_right (left a) (left b) placed_distinct, inner_zero_right]
      exact sub_eq_zero.mp (by simpa only [inner_sub_right] using zero)
    have apex_bound : inner ℝ n (right apex) ≤ inner ℝ n (left a) := by
      have bound : inner ℝ n (right apex - left a) ≤ 0 := by
        rw [hingeSideVector_inner (left a) (left b) (left c) (right apex) placed_distinct]
        exact outward
      exact sub_nonpos.mp (by simpa only [inner_sub_right] using bound)
    have side_bound := F.upper_bound_of_vertices right (innerSL ℝ n) (inner ℝ n (left a)) (by
      intro x hx
      rw [vertices] at hx
      rcases hx with rfl | rfl | rfl
      · change inner ℝ n (right a) ≤ inner ℝ n (left a)
        rw [at_a]
      · change inner ℝ n (right b) ≤ inner ℝ n (left a)
        rw [at_b, edge_height]
      · exact apex_bound)
    apply Disjoint.symm
    apply disjoint_interiors_of_halfplanes (innerSL ℝ n) (plane_inner_height_surjective nonzero)
      (inner ℝ n (left a))
    · rintro _ ⟨x, xF, rfl⟩
      exact side_bound x xF
    · rintro _ ⟨x, xB, rfl⟩
      exact base_bound x xB
  · intro x xB xF
    have ax : a ≠ x := fun same => xF (same ▸ aF)
    have bx : b ≠ x := fun same => xF (same ▸ bF)
    apply two_triangles_distance_gt a b x apex (left a) (left b) (left x) (right apex)
      (fun same => ab (Subtype.ext same)) edge_length (left_rigid a aB x xB) (left_rigid b bB x xB)
      (by simpa only [at_a] using right_rigid a aF apex apexF)
      (by simpa only [at_b] using right_rigid b bF apex apexF) (all_outward x xB)
    · exact P.no_three_collinear_vertices a.property b.property x.property
        (fun same => ab (Subtype.ext same)) (fun same => ax (Subtype.ext same))
        (fun same => bx (Subtype.ext same))
    · intro in_plane
      apply base.outside_affineSpan (P.vertices_subset_body apex.property) apex_outside
      apply affineSpan_mono ℝ (show ({(a : Space), (b : Space), (x : Space)} : Set Space) ⊆ base.val from ?_) in_plane
      rintro y (rfl | rfl | rfl)
      exacts [aB, bB, xB]

end SixVertexUnfolding.ConvexPolyhedron.Face
