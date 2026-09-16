import SixVertexUnfolding.Geometry.ConvexSurfaceFolding
import SixVertexUnfolding.Geometry.ConvexFiniteSelection
import SixVertexUnfolding.Geometry.SurfaceFlatCharts

/-! Finite nonexpanding face formulas give exact intrinsic distances on
convex patches of any actual flat surface chart, including across original hinges. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A radial development is isometric on a contained convex flat-chart patch. -/
theorem finite_development_flat_patch_isometric {P : ConvexPolyhedron} {ι : Type*} [Finite ι]
    (region : Set (frontier P.body)) (planar : Set Plane) (convex_planar : Convex ℝ planar)
    (H : region ≃ₜ planar) (maps : ι → Space → Plane) (nonexpanding : ∀ i, LipschitzWith 1 (maps i))
    (selected : ∀ x, ∃ i, (H x : Plane) = maps i (x.val : Space))
    (inverse_bound : LipschitzWith 1 (fun z => ((H.symm z).val : Space)))
    {z : Space} (chart : P.FlatChart z) (patch : Set Plane) (convex_patch : Convex ℝ patch)
    (in_domain : patch ⊆ chart.domain) (inclusion : C(patch, region))
    (located : ∀ x, ((inclusion x).val : Space) = chart.map (x : Plane)) :
    Isometry (fun x => (H (inclusion x) : Plane)) := by
  have forward : LipschitzWith 1 (fun x => (H (inclusion x) : Plane)) := by
    apply convex_subtype_finite_selection_lipschitz patch convex_patch
      (fun x => (H (inclusion x) : Plane)) (fun i x => maps i (chart.map x)) 1
      (continuous_subtype_val.comp (H.continuous.comp inclusion.continuous))
    · intro i
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have bound := (nonexpanding i).dist_le_mul (chart.map x) (chart.map y)
      have chord := P.dist_le_surfaceDist (chart.on_surface (in_domain hx)) (chart.on_surface (in_domain hy))
      rw [chart.distance x (in_domain hx) y (in_domain hy)] at chord
      simpa only [NNReal.coe_one, one_mul] using
        (show dist (maps i (chart.map x)) (maps i (chart.map y)) ≤ dist x y from
          (by simpa using bound : dist (maps i (chart.map x)) (maps i (chart.map y)) ≤
            dist (chart.map x) (chart.map y)).trans chord)
    · intro x
      obtain ⟨i, hi⟩ := selected (inclusion x)
      exact ⟨i, hi.trans (congrArg (maps i) (located x))⟩
  have backward (x y : planar) :
      P.surfaceDist (H.symm x).val (H.symm y).val ≤ dist (x : Plane) (y : Plane) :=
    convex_folding_surface_distance planar convex_planar
      ⟨fun w => (H.symm w).val, continuous_subtype_val.comp H.symm.continuous⟩ inverse_bound x y
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa using forward.dist_le_mul x y
  · have bound := backward (H (inclusion x)) (H (inclusion y))
    rw [H.symm_apply_apply, H.symm_apply_apply, located, located,
      chart.distance x (in_domain x.property) y (in_domain y.property)] at bound
    exact bound

end SixVertexUnfolding.ConvexPolyhedron
