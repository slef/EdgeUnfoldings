import SixVertexUnfolding.Geometry.TrianglePetal
import SixVertexUnfolding.Geometry.VertexCertificate
import SixVertexUnfolding.Geometry.HingeSideOrder

/-! Unfold a whole polygonal facet outward across an original edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron}

/-- Distinct whole facets have an original vertex belonging to the first alone. -/
theorem exists_vertex_not_mem_face (F G : P.Face) (different : F ≠ G) :
    ∃ v : P.Vertex, (v : Space) ∈ F.val ∧ (v : Space) ∉ G.val := by
  by_contra none
  push Not at none
  apply different
  apply F.eq_of_subset G
  rw [F.eq_convexHull_vertices]
  apply convexHull_min _ G.convex
  rintro x ⟨in_face, vertex⟩
  exact none ⟨x, vertex⟩ in_face

/-- A whole neighboring facet can be placed outward; all its free vertices move farther from every missing base vertex. -/
theorem exists_polygon_petal (base F : P.Face) (shared : P.ShareEdge base F)
    (left : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ base.val, ∀ y ∈ base.val, dist (left x) (left y) = dist x y) :
    ∃ right : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ F.val, ∀ y ∈ F.val, dist (right x) (right y) = dist x y) ∧
      Set.EqOn left right (base.val ∩ F.val) ∧
      Disjoint (interior (left '' base.val)) (interior (right '' F.val)) ∧
      (∀ x y : P.Vertex, (x : Space) ∈ base.val → (x : Space) ∉ F.val →
        (y : Space) ∈ F.val → (y : Space) ∉ base.val →
        dist (x : Space) y < dist (left x) (right y)) ∧
      (∀ a ∈ (base.val ∩ F.val) ∩ (P.vertices : Set Space),
        ∀ b ∈ (base.val ∩ F.val) ∩ (P.vertices : Set Space), a ≠ b →
        ∀ x ∈ base.val, ∀ y ∈ F.val, OppositeHingeSides (left a) (left b) (left x) (right y)) := by
  have different : base ≠ F := by rintro rfl; exact base.shareEdge_irrefl shared
  obtain ⟨a, b, ab, common⟩ := base.shared_vertices_eq_pair F shared
  have a_in : a ∈ (base.val ∩ F.val) ∩ (P.vertices : Set Space) := by rw [common]; simp
  have b_in : b ∈ (base.val ∩ F.val) ∩ (P.vertices : Set Space) := by rw [common]; simp
  obtain ⟨c, cB, cF⟩ := base.exists_vertex_not_mem_face F different
  obtain ⟨d, dF, dB⟩ := F.exists_vertex_not_mem_face base different.symm
  have abc := P.no_three_collinear_vertices a_in.2 b_in.2 c.property ab
    (fun same => cF (same ▸ a_in.1.2)) (fun same => cF (same ▸ b_in.1.2))
  have abd := P.no_three_collinear_vertices a_in.2 b_in.2 d.property ab
    (fun same => dB (same ▸ a_in.1.1)) (fun same => dB (same ▸ b_in.1.1))
  have length := left_rigid a a_in.1.1 b b_in.1.1
  have placed_distinct : left a ≠ left b := by
    intro same
    exact ab (dist_eq_zero.mp (by simpa [same] using length.symm))
  obtain ⟨right, rigid, at_a, at_b, outward⟩ :=
    F.exists_outward_placement a b c d a_in.1.2 b_in.1.2 left length placed_distinct
  have base_side (x : Space) (hx : x ∈ base.val) :=
    base.placed_hinge_side F left a b c x a_in.1.1 b_in.1.1 cB hx
      a_in.1.2 b_in.1.2 cF abc placed_distinct
  have petal_side (y : Space) (hy : y ∈ F.val) :
      ∃ v : ℝ, 0 ≤ v ∧ hingeSideVector (left a) (left b) (right y) =
        v • hingeSideVector (left a) (left b) (right d) := by
    have right_distinct : right a ≠ right b := by simpa only [at_a, at_b] using placed_distinct
    simpa only [at_a, at_b] using F.placed_hinge_side base right a b d y
      a_in.1.2 b_in.1.2 dF hy a_in.1.1 b_in.1.1 dB abd right_distinct
  have all_outward (x y : Space) (hx : x ∈ base.val) (hy : y ∈ F.val) :
      OppositeHingeSides (left a) (left b) (left x) (right y) := by
    obtain ⟨u, hu, eu⟩ := base_side x hx
    obtain ⟨v, hv, ev⟩ := petal_side y hy
    change inner ℝ (hingeSideVector (left a) (left b) (left x))
      (hingeSideVector (left a) (left b) (right y)) ≤ 0
    rw [eu, ev, real_inner_smul_left, inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hu (mul_nonpos_of_nonneg_of_nonpos hv outward)
  refine ⟨right, rigid, ?_, ?_, ?_, ?_⟩
  · apply base.joined_of_vertex_agreement F left right
    intro x hx
    rw [common] at hx
    rcases hx with rfl | rfl
    exacts [at_a.symm, at_b.symm]
  · let n := hingeSideVector (left a) (left b) (left c)
    have placed_triangle := P.placed_triangle_noncollinear
      ⟨a, a_in.2⟩ ⟨b, b_in.2⟩ c
      (fun same => ab (congrArg Subtype.val same))
      (fun same => cF (congrArg Subtype.val same ▸ a_in.1.2))
      (fun same => cF (congrArg Subtype.val same ▸ b_in.1.2))
      (left a) (left b) (left c) length
      (left_rigid a a_in.1.1 c cB) (left_rigid b b_in.1.1 c cB)
    have nonzero : n ≠ 0 := hingeSideVector_ne_zero _ _ _ placed_triangle
    apply Disjoint.symm
    apply disjoint_interiors_of_halfplanes (innerSL ℝ n) (plane_inner_height_surjective nonzero)
      (inner ℝ n (left a))
    · rintro _ ⟨y, hy, rfl⟩
      have bound : inner ℝ n (right y - left a) ≤ 0 := by
        rw [hingeSideVector_inner (left a) (left b) (left c) (right y) placed_distinct]
        exact all_outward c y cB hy
      exact sub_nonpos.mp (by simpa only [inner_sub_right] using bound)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨u, hu, eu⟩ := base_side x hx
      have bound : 0 ≤ inner ℝ n (left x - left a) := by
        rw [hingeSideVector_inner (left a) (left b) (left c) (left x) placed_distinct,
          eu, inner_smul_right]
        exact mul_nonneg hu real_inner_self_nonneg
      exact sub_nonneg.mp (by simpa only [inner_sub_right] using bound)
  · intro x y xB xF yF yB
    apply two_triangles_distance_gt a b x y (left a) (left b) (left x) (right y) ab length
      (left_rigid a a_in.1.1 x xB) (left_rigid b b_in.1.1 x xB)
      (by simpa only [at_a] using rigid a a_in.1.2 y yF)
      (by simpa only [at_b] using rigid b b_in.1.2 y yF) (all_outward x y xB yF)
    · exact P.no_three_collinear_vertices a_in.2 b_in.2 x.property ab
        (fun same => xF (same ▸ a_in.1.2)) (fun same => xF (same ▸ b_in.1.2))
    · intro in_plane
      apply base.outside_affineSpan (P.vertices_subset_body y.property) yB
      apply affineSpan_mono ℝ (show ({a, b, (x : Space)} : Set Space) ⊆ base.val from ?_) in_plane
      rintro z (rfl | rfl | rfl)
      exacts [a_in.1.1, b_in.1.1, xB]
  · intro a' ha' b' hb' distinct x hx y hy
    have swapped := (oppositeHingeSides_swap (left a) (left b) (left x) (right y) placed_distinct).mpr
      (all_outward x y hx hy)
    rw [common] at ha' hb'
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact (distinct rfl).elim
    · exact all_outward x y hx hy
    · exact swapped
    · exact (distinct rfl).elim

end SixVertexUnfolding.ConvexPolyhedron.Face
