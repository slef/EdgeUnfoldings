import SixVertexUnfolding.Geometry.SurfaceDistance

/-! Intrinsic distance is continuous for the actual boundary topology. A finite
closed cover by original facets lets us prove this without assuming a surface chart. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter
open scoped Topology

/-- Distance from a fixed boundary point is 1-Lipschitz on each original facet. -/
theorem surfaceDist_lipschitz_on_face (P : ConvexPolyhedron) {a : Space}
    (ha : a ∈ frontier P.body) (F : P.Face) : LipschitzOnWith 1 (P.surfaceDist a) F.val := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have xy := P.surfaceDist_triangle ha (F.subset_frontier hx) (F.subset_frontier hy)
  have yx := P.surfaceDist_triangle ha (F.subset_frontier hy) (F.subset_frontier hx)
  rw [P.surfaceDist_eq_dist_in_face F hx hy] at xy
  rw [P.surfaceDist_eq_dist_in_face F hy hx, dist_comm y x] at yx
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The original closed facets cover exactly the topological boundary. -/
theorem boundary_eq_union_faces (P : ConvexPolyhedron) : frontier P.body = ⋃ F : P.Face, F.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨F, xF⟩ := P.boundary_point_in_face hx
    exact mem_iUnion.mpr ⟨F, xF⟩
  · intro hx
    obtain ⟨F, xF⟩ := mem_iUnion.mp hx
    exact F.subset_frontier xF

/-- Intrinsic distance to a fixed source is continuous across edges and vertices. -/
theorem surfaceDist_continuousOn (P : ConvexPolyhedron) {a : Space}
    (ha : a ∈ frontier P.body) : ContinuousOn (P.surfaceDist a) (frontier P.body) := by
  rw [P.boundary_eq_union_faces]
  exact (locallyFinite_of_finite (fun F : P.Face => F.val)).continuousOn_iUnion
    (fun F => F.isClosed) (fun F => (P.surfaceDist_lipschitz_on_face ha F).continuousOn)

/-- The two-point intrinsic distance is jointly continuous in the boundary topology. -/
theorem surfaceDist_continuous (P : ConvexPolyhedron) :
    Continuous (fun pair : (frontier P.body) × (frontier P.body) => P.surfaceDist pair.1 pair.2) := by
  apply continuous_iff_continuousAt.mpr
  intro pair
  apply Metric.tendsto_nhds.mpr
  intro ε positive
  have first : Continuous (fun x : frontier P.body => P.surfaceDist pair.1 x) :=
    (P.surfaceDist_continuousOn pair.1.property).restrict
  have second : Continuous (fun x : frontier P.body => P.surfaceDist pair.2 x) :=
    (P.surfaceDist_continuousOn pair.2.property).restrict
  have small_first : ∀ᶠ q : (frontier P.body) × (frontier P.body) in 𝓝 pair,
      P.surfaceDist pair.1 q.1 < ε / 2 := by
    have near := (first.comp continuous_fst).continuousAt.eventually_lt_const (show P.surfaceDist pair.1 pair.1 < ε / 2 by
      rw [P.surfaceDist_self pair.1.property]; exact half_pos positive)
    exact near
  have small_second : ∀ᶠ q : (frontier P.body) × (frontier P.body) in 𝓝 pair,
      P.surfaceDist pair.2 q.2 < ε / 2 := by
    exact (second.comp continuous_snd).continuousAt.eventually_lt_const (show P.surfaceDist pair.2 pair.2 < ε / 2 by
      rw [P.surfaceDist_self pair.2.property]; exact half_pos positive)
  filter_upwards [small_first, small_second] with q hfirst hsecond
  have upper := P.surfaceDist_triangle q.1.property pair.1.property q.2.property
  have upper_tail := P.surfaceDist_triangle pair.1.property pair.2.property q.2.property
  have lower := P.surfaceDist_triangle pair.1.property q.1.property pair.2.property
  have lower_tail := P.surfaceDist_triangle q.1.property q.2.property pair.2.property
  rw [P.surfaceDist_comm (q.1 : Space) pair.1] at upper
  rw [P.surfaceDist_comm (q.2 : Space) pair.2] at lower_tail
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end SixVertexUnfolding.ConvexPolyhedron
