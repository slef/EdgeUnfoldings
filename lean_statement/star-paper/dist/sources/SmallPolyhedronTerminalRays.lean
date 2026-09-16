import SixVertexUnfolding.Geometry.SmallPolyhedronRayExtensions
import SixVertexUnfolding.Geometry.CutSetTerminalRays
import SixVertexUnfolding.Geometry.SameSourceGeodesics

/-! A shortest route cannot pass through a cut point and continue. Equal-length
shortest rays from the same source agree if they meet internally. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- A shortest route cannot pass through a multiple-route target before its final endpoint. -/
theorem small_shortest_route_avoids_multiple_locus (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (t : unitInterval) (before : t < 1) :
    (f t : Space) ∉ P.multipleRouteLocus (f 0) := by
  rw [P.multiple_routes_iff_fiber (f 0) (f t)]
  rintro ⟨_, multiple⟩
  exact multiple (small_geodesic_interior_targets_unique size small_faces f geodesic different t before)

include size small_faces in
/-- Unique-route targets are dense in the whole boundary, including neighborhoods of edges and vertices. -/
theorem small_uniqueTargets_dense (a : frontier P.body) : Dense (P.uniqueTargets a) := by
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
  have unique := small_geodesic_interior_targets_unique size small_faces f hf.1
    (by simpa only [first, last] using same) t before
  simpa only [first] using unique

include size small_faces in
/-- The multiple-route locus has empty interior in the actual boundary topology. -/
theorem small_multiple_route_locus_interior_empty (a : frontier P.body) :
    interior {b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} = ∅ := by
  have dense := small_uniqueTargets_dense size small_faces a
  rw [P.uniqueTargets_eq_complement_multiple a] at dense
  exact interior_eq_empty_iff_dense_compl.mpr dense

include size small_faces in
/-- Proper prefixes of every shortest route avoid the vertex-augmented cut set. -/
theorem small_geodesic_proper_prefix_outside_cutSet (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (t : unitInterval) (before : t < 1) : f t ∉ P.cutSet (f 0) := by
  by_cases at_start : t = 0
  · subst t
    exact P.source_not_cutSet (f 0)
  rintro (multiple | vertex)
  · exact small_shortest_route_avoids_multiple_locus size small_faces f geodesic different t before multiple
  · obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
    exact small_shortest_lipschitz_avoids_vertices size small_faces (P.surfacePathOfCurve f)
      (fun equal => different (Subtype.ext equal)) shortest finite speed t
      (lt_of_le_of_ne t.property.1 (Ne.symm at_start)) before vertex.1

include size small_faces in
/-- A shortest extension through a cut point has that very point as its endpoint. -/
theorem small_shortest_extension_of_cut_point (a b c : frontier P.body) (cut : b ∈ P.cutSet a)
    (extension : c ∈ P.shortestExtensions a b) : c = b := by
  obtain ⟨f, hf, t, at_t⟩ := P.shortest_extension_path a b c extension
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = c := congrArg Prod.snd hf.2
  have different : f 0 ≠ f 1 := by
    intro equal
    have at_start := P.geodesic_same_endpoints f hf.1 equal t
    rw [at_t, first] at at_start
    exact P.source_not_cutSet a (at_start ▸ cut)
  by_contra cb
  have before : t < 1 := lt_of_le_of_ne t.property.2 (fun one => cb (by simpa only [one, last] using at_t))
  have outside := small_geodesic_proper_prefix_outside_cutSet size small_faces f hf.1 different t before
  rw [first, at_t] at outside
  exact outside cut

include size small_faces in
/-- Away from the source, being in the cut set means having no strict shortest extension. -/
theorem small_cutSet_iff_terminal (a b : frontier P.body) (different : a ≠ b) :
    b ∈ P.cutSet a ↔ ∀ c ∈ P.shortestExtensions a b, c = b := by
  constructor
  · exact fun cut c extension => small_shortest_extension_of_cut_point size small_faces a b c cut extension
  · intro terminal
    by_contra outside
    obtain ⟨c, extension, different_c⟩ := small_shortest_extension_outside_cutSet size small_faces a b different outside
    exact different_c (terminal c extension)

include size small_faces in
/-- Interior meeting identifies the entire two equal-length rays, including their endpoints. -/
theorem small_same_source_geodesics_agree (f g : P.BoundaryCurve)
    (hf : f ∈ P.geodesicCurves) (hg : g ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (source : f 0 = g 0)
    (same_length : P.surfaceDist (f 0) (f 1) = P.surfaceDist (g 0) (g 1))
    (t : unitInterval) (positive : 0 < t) (before : t < 1) (meet : f t = g t) : f = g := by
  let first := P.surfacePathOfCurve f
  let second := (P.surfacePathOfCurve g).cast (congrArg Subtype.val source) rfl
  obtain ⟨first_shortest, first_finite, first_speed⟩ := P.surfacePathOfCurve_shortest f hf
  obtain ⟨second_shortest, second_finite, second_speed⟩ := P.surfacePathOfCurve_shortest g hg
  have lengths : first.length = second.length := by
    apply (ENNReal.toReal_eq_toReal_iff' first_finite second_finite).mp
    rw [first.length_eq_surfaceEDist first_shortest]
    change P.surfaceDist (f 0) (f 1) = (P.surfacePathOfCurve g).length.toReal
    rw [(P.surfacePathOfCurve g).length_eq_surfaceEDist second_shortest]
    exact same_length
  have equal := first.same_source_agree_of_meeting second first_shortest
    ((P.surfacePathOfCurve g).cast_shortest (congrArg Subtype.val source) rfl second_shortest)
    first_finite second_finite first_speed second_speed lengths
    (small_shortest_lipschitz_avoids_vertices size small_faces first
      (fun same => different (Subtype.ext same)) first_shortest first_finite first_speed)
    t positive before (congrArg Subtype.val meet)
  apply BoundedContinuousFunction.ext
  intro u
  exact Subtype.ext (equal u)

end SixVertexUnfolding.ConvexPolyhedron
