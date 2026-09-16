import SixVertexUnfolding.Geometry.ConeHalfplanes
import SixVertexUnfolding.Geometry.VoronoiSeparation
import SixVertexUnfolding.Geometry.TriangleStrictComparison

/-! The two outward faces of a spatial trihedral corner are separated by the bisector of their apex copies. -/

namespace SixVertexUnfolding

/-- A nearest-site inequality extends along a whole corner cone if its origin is equidistant from the sites. -/
theorem corner_cone_nearer_site (o a p q : Plane)
    (at_origin : dist o p = dist o q) (at_ray : dist a p ≤ dist a q) :
    ∀ x ∈ translatedCone o (a - o) (p - o), dist x p ≤ dist x q := by
  have origin_le := (nearer_site_iff_halfplane o p q).mp at_origin.le
  have origin_ge := (nearer_site_iff_halfplane o q p).mp at_origin.symm.le
  have origin_height : inner ℝ (q - p) o = (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2 := by
    simp only [inner_sub_left] at origin_le origin_ge ⊢
    linarith
  have ray := (nearer_site_iff_halfplane a p q).mp at_ray
  have site := (nearer_site_iff_halfplane p p q).mp (by simp)
  rintro x ⟨t, u, ht, hu, expression⟩
  apply (nearer_site_iff_halfplane x p q).mpr
  have projected := congrArg (fun v => inner ℝ (q - p) v) expression
  simp only [inner_sub_right, inner_add_right, inner_smul_right] at projected
  have first := mul_nonpos_of_nonneg_of_nonpos ht (show inner ℝ (q - p) a - inner ℝ (q - p) o ≤ 0 by linarith)
  have second := mul_nonpos_of_nonneg_of_nonpos hu (show inner ℝ (q - p) p - inner ℝ (q - p) o ≤ 0 by linarith)
  linarith

/-- Two source copies give a separator for the entire infinite corner cones. -/
theorem corner_cones_disjoint_of_nearer_sites (o a b p q : Plane) (distinct : p ≠ q)
    (at_origin : dist o p = dist o q)
    (left : dist a p ≤ dist a q) (right : dist b q ≤ dist b p) :
    Disjoint (interior (translatedCone o (a - o) (p - o)))
      (interior (translatedCone o (b - o) (q - o))) :=
  disjoint_interiors_of_nearer_sites p q distinct
    (corner_cone_nearer_site o a p q at_origin left)
    (corner_cone_nearer_site o b q p at_origin.symm right)

/-- Flattening two faces outward from a third at a nonflat spatial corner separates both full corner cones. -/
theorem outward_trihedral_cones_disjoint (a b c d : Space) (A B C D₁ D₂ : Plane)
    (ab : a ≠ b) (ac : a ≠ c)
    (base_triangle : ¬ Collinear ℝ ({a, b, c} : Set Space))
    (spatial : d ∉ affineSpan ℝ ({a, b, c} : Set Space))
    (AB : dist A B = dist a b) (AC : dist A C = dist a c) (BC : dist B C = dist b c)
    (AD₁ : dist A D₁ = dist a d) (BD₁ : dist B D₁ = dist b d)
    (AD₂ : dist A D₂ = dist a d) (CD₂ : dist C D₂ = dist c d)
    (left_outward : OppositeHingeSides A B C D₁)
    (right_outward : OppositeHingeSides A C B D₂) :
    Disjoint (interior (translatedCone A (B - A) (D₁ - A)))
      (interior (translatedCone A (C - A) (D₂ - A))) := by
  have permute : ({a, c, b} : Set Space) = {a, b, c} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have first := two_triangles_distance_gt a c b d A C B D₂ ac AC AB
    (by simpa only [dist_comm] using BC) AD₂ CD₂ right_outward
    (by simpa only [permute] using base_triangle) (by simpa only [permute] using spatial)
  have second := two_triangles_distance_gt a b c d A B C D₁ ab AB AC BC AD₁ BD₁
    left_outward base_triangle spatial
  have distinct : D₁ ≠ D₂ := by
    intro same
    rw [← BD₁, same] at first
    exact first.false
  exact corner_cones_disjoint_of_nearer_sites A B C D₁ D₂ distinct
    (AD₁.trans AD₂.symm) (by linarith) (by linarith)

end SixVertexUnfolding
