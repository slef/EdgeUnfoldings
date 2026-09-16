import SixVertexUnfolding.Geometry.SurfaceTopology
import Mathlib.Analysis.Convex.Contractible

/-! Stereographic projection makes the polyhedral boundary minus any one
point homeomorphic to the plane, hence contractible. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The punctured polyhedral sphere is homeomorphic to the ordinary plane. -/
theorem punctured_boundary_homeomorph_plane (P : ConvexPolyhedron) (a : frontier P.body) :
    Nonempty ({b : frontier P.body // b ≠ a} ≃ₜ Plane) := by
  obtain ⟨h, boundary_eq⟩ := P.exists_spherical_homeomorphism
  let sphereMap : frontier P.body ≃ₜ Metric.sphere (0 : Space) 1 :=
    (h.image (frontier P.body)).trans (Homeomorph.setCongr boundary_eq)
  letI : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨by simp [Space]⟩
  let chart := stereographic' 2 (sphereMap a)
  have source_iff (b : frontier P.body) : b ≠ a ↔ sphereMap b ∈ chart.source := by
    simp only [chart, stereographic'_source, mem_compl_iff, mem_singleton_iff]
    exact not_congr sphereMap.injective.eq_iff.symm
  let puncture : {b : frontier P.body // b ≠ a} ≃ₜ chart.source := sphereMap.subtype source_iff
  let target : chart.target ≃ₜ Plane :=
    (Homeomorph.setCongr (stereographic'_target (sphereMap a))).trans (Homeomorph.Set.univ Plane)
  exact ⟨(puncture.trans chart.toHomeomorphSourceTarget).trans target⟩

/-- There is no topological obstruction to contracting the boundary with one point removed. -/
theorem punctured_boundary_contractible (P : ConvexPolyhedron) (a : frontier P.body) :
    ContractibleSpace {b : frontier P.body // b ≠ a} := by
  obtain ⟨h⟩ := P.punctured_boundary_homeomorph_plane a
  exact h.contractibleSpace

end SixVertexUnfolding.ConvexPolyhedron
