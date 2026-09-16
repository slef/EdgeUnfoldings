import SixVertexUnfolding.Geometry.RecoveredSourceDistance
import SixVertexUnfolding.Geometry.OctahedralVertexAvoidance

/-! A terminal source is the single point from which a route's final
straight portion develops. This records actual route data, not just a candidate. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- In the final face, the route eventually follows the straight line from this source copy. -/
def HasTerminalSource (P : ConvexPolyhedron) (f : P.BoundaryCurve) (F : P.Face) (source : Plane) : Prop :=
  ∃ start : unitInterval, start < 1 ∧ ∀ t ∈ Icc start 1, (f t : Space) ∈ F.val ∧
    P.faceCoordinates F (f t) = AffineMap.lineMap source (P.faceCoordinates F (f 1)) (t : ℝ)

namespace HasTerminalSource

variable {P : ConvexPolyhedron} {f : P.BoundaryCurve} {F : P.Face} {source other : Plane}

theorem target_in_face (terminal : P.HasTerminalSource f F source) : (f 1 : Space) ∈ F.val := by
  obtain ⟨start, _, tail⟩ := terminal
  exact (tail 1 ⟨unitInterval.le_one', le_rfl⟩).1

/-- The terminal source of one route in fixed face coordinates is unique. -/
theorem unique (terminal : P.HasTerminalSource f F source) (second : P.HasTerminalSource f F other) :
    source = other := by
  obtain ⟨s, s_before, first⟩ := terminal
  obtain ⟨u, u_before, second⟩ := second
  obtain ⟨t, after, before⟩ := exists_between (max_lt s_before u_before)
  exact lineMap_left_unique source other (P.faceCoordinates F (f 1)) t (show (t : ℝ) < 1 from before).ne
    ((first t ⟨(le_max_left s u).trans after.le, before.le⟩).2.symm.trans
      (second t ⟨(le_max_right s u).trans after.le, before.le⟩).2)

/-- The terminal source distance is the full intrinsic distance of a geodesic. -/
theorem distance (terminal : P.HasTerminalSource f F source) (geodesic : f ∈ P.geodesicCurves) :
    P.surfaceDist (f 0) (f 1) = dist source (P.faceCoordinates F (f 1)) := by
  obtain ⟨s, before, tail⟩ := terminal
  have at_s := tail s ⟨le_rfl, unitInterval.le_one'⟩
  have target := (tail 1 ⟨unitInterval.le_one', le_rfl⟩).1
  rw [P.recoveredSource_distance f geodesic F s before at_s.1 target,
    P.recoveredSource_eq F s before f source at_s.2]

/-- An actual terminal source also gives the intrinsic distance at every point of its final straight portion. -/
theorem distance_at (terminal : P.HasTerminalSource f F source) (geodesic : f ∈ P.geodesicCurves)
    (t : unitInterval) (coordinates : P.faceCoordinates F (f t) =
      AffineMap.lineMap source (P.faceCoordinates F (f 1)) (t : ℝ)) :
    P.surfaceDist (f 0) (f t) = dist source (P.faceCoordinates F (f t)) := by
  rw [geodesic 0 t, terminal.distance geodesic, coordinates, dist_left_lineMap,
    Real.norm_eq_abs, abs_of_nonneg t.property.1]
  have elapsed : dist (0 : unitInterval) t = (t : ℝ) := by
    change dist (0 : ℝ) (t : ℝ) = _
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg t.property.1]
  rw [elapsed, mul_comm]

/-- Recovering the source from any earlier point in the final face gives this same actual source. -/
theorem recovered_eq (terminal : P.HasTerminalSource f F source) (geodesic : f ∈ P.geodesicCurves)
    (t : unitInterval) (before : t < 1) (inside : (f t : Space) ∈ F.val) :
    P.recoveredSource F t f = source := by
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨start, start_before, tail⟩ := terminal
  have formula := (P.surfacePathOfCurve f).terminal_formula_extends shortest finite speed F
    (tail 1 ⟨unitInterval.le_one', le_rfl⟩).1 source start start_before (fun u hu => (tail u hu).2)
    t before inside
  exact P.recoveredSource_eq F t before f source formula

end HasTerminalSource

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every canonical geodesic ending in a unique face has an actual terminal source in the fixed finite list. -/
theorem exists_terminal_source (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face) (unique_face : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F) :
    ∃ source ∈ P.sourceImages (f 0) F, P.HasTerminalSource f F source := by
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨code, start, before, tail⟩ := (P.surfacePathOfCurve f).exists_terminal_source_code shortest finite speed
    (graph.shortest_lipschitz_avoids_vertices small_faces _ (fun h => different (Subtype.ext h)) shortest finite speed)
  have target : (f 1 : Space) ∈ (code.face code.last).val := (tail 1 ⟨unitInterval.le_one', le_rfl⟩).1
  have same := unique_face (code.face code.last) target
  refine ⟨code.sourceImage (f 0), ⟨⟨code, same⟩, rfl⟩, start, before, ?_⟩
  intro t ht
  simpa only [same] using tail t ht

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
