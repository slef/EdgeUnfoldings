import SixVertexUnfolding.Geometry.ShortestExtensionUniqueness
import SixVertexUnfolding.Geometry.MultipleRouteTopology

/-! A shortest route meets the multiple-route locus only at its final
endpoint. Approaching any target along a shortest route proves density of
the unique-route targets in the entire actual boundary. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A shortest route cannot pass through a multiple-route target before its final endpoint. -/
theorem shortest_route_avoids_multiple_locus (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (t : unitInterval) (before : t < 1) :
    (f t : Space) ∉ P.multipleRouteLocus (f 0) := by
  rw [P.multiple_routes_iff_fiber (f 0) (f t)]
  rintro ⟨_, multiple⟩
  exact multiple (graph.geodesic_interior_targets_unique small_faces f geodesic different t before)

include graph small_faces in
/-- Unique-route targets are dense in the whole boundary, including neighborhoods of edges and vertices. -/
theorem uniqueTargets_dense (a : frontier P.body) : Dense (P.uniqueTargets a) := by
  intro b
  by_cases same : a = b
  · subst b
    exact subset_closure (P.geodesicFiber_self a)
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  apply mem_closure_iff.mpr
  intro U openU bU
  have one_in : (1 : unitInterval) ∈ f ⁻¹' U := by simpa only [mem_preimage, last] using bU
  obtain ⟨ε, positive, contained⟩ := Metric.isOpen_iff.mp (openU.preimage f.continuous) 1 one_in
  obtain ⟨r, after, before⟩ := exists_between (show max (0 : ℝ) (1 - ε) < 1 from
    max_lt (by norm_num) (by linarith))
  let t : unitInterval := ⟨r, ((le_max_left _ _).trans_lt after).le, before.le⟩
  have near : t ∈ Metric.ball (1 : unitInterval) ε := by
    rw [Metric.mem_ball]
    change dist r (1 : ℝ) < ε
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr before)]
    have bound := (le_max_right (0 : ℝ) (1 - ε)).trans_lt after
    linarith
  refine ⟨f t, contained near, ?_⟩
  have unique := graph.geodesic_interior_targets_unique small_faces f hf.1
    (by simpa only [first, last] using same) t before
  simpa only [first] using unique

include graph small_faces in
/-- The multiple-route locus has empty interior in the actual boundary topology. -/
theorem multiple_route_locus_interior_empty (a : frontier P.body) :
    interior {b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} = ∅ := by
  have dense := graph.uniqueTargets_dense small_faces a
  rw [P.uniqueTargets_eq_complement_multiple a] at dense
  exact interior_eq_empty_iff_dense_compl.mpr dense

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
