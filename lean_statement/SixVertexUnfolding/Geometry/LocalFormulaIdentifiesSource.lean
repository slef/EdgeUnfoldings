import SixVertexUnfolding.Geometry.TerminalSourceData
import SixVertexUnfolding.Geometry.UniqueRouteSourceDistance

/-! A local source-distance formula along the interior of a terminal
straight portion must use that portion's actual source copy. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Two radial distance formulas agreeing along a nonconstant straight route have the same source. -/
theorem local_formula_identifies_source (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (F : P.Face) (source other : Plane)
    (terminal : P.HasTerminalSource f F source)
    (start : unitInterval) (tail : ∀ t ∈ Icc start 1, (f t : Space) ∈ F.val ∧
      P.faceCoordinates F (f t) = AffineMap.lineMap source (P.faceCoordinates F (f 1)) (t : ℝ))
    (m : unitInterval) (after_start : start ≤ m) (positive : 0 < m) (before : m < 1)
    (U : Set Space) (openU : IsOpen U) (fmU : (f m : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist (f 0) x = dist other (P.faceCoordinates F x)) :
    other = source := by
  let path := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨s, v, sm, mv, near⟩ := path.interval_inside_neighborhood m positive before U openU fmU
  obtain ⟨u, mu, uv⟩ := exists_between mv
  have u_before : u < 1 := uv.trans_le unitInterval.le_one'
  have fuU : (f u : Space) ∈ U := near u ⟨sm.le.trans mu.le, uv.le⟩
  have at_m := tail m ⟨after_start, before.le⟩
  have at_u := tail u ⟨after_start.trans mu.le, u_before.le⟩
  have source_distance (r : unitInterval) : P.surfaceDist (f 0) (f r) = path.length.toReal * (r : ℝ) :=
    path.source_distance shortest finite speed r
  have between : dist (P.faceCoordinates F (f m)) (P.faceCoordinates F (f u)) =
      path.length.toReal * ((u : ℝ) - (m : ℝ)) := by
    rw [P.faceCoordinates_rigid F _ at_m.1 _ at_u.1,
      ← P.surfaceDist_eq_dist_in_face F at_m.1 at_u.1]
    change P.surfaceDist (path.curve m) (path.curve u) = _
    rw [path.surfaceDist_along shortest finite speed]
    congr 1
    change dist (m : ℝ) (u : ℝ) = _
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (show (m : ℝ) < u from mu))]
    ring
  have radial (q : Plane)
      (first : dist q (P.faceCoordinates F (f m)) = path.length.toReal * (m : ℝ))
      (last : dist q (P.faceCoordinates F (f u)) = path.length.toReal * (u : ℝ)) :
      P.faceCoordinates F (f m) = AffineMap.lineMap q (P.faceCoordinates F (f u)) ((m : ℝ) / (u : ℝ)) := by
    simpa only [sub_zero] using point_eq_lineMap_of_distance_ratios q (P.faceCoordinates F (f u))
      (P.faceCoordinates F (f m)) 0 m u path.length.toReal (positive.trans mu) m.property.1 mu.le
      (by simpa using first) between (by simpa using last)
  have actual := radial source
    ((terminal.distance_at geodesic m at_m.2).symm.trans (source_distance m))
    ((terminal.distance_at geodesic u at_u.2).symm.trans (source_distance u))
  have candidate := radial other
    ((formula _ ⟨fmU, (f m).property⟩).symm.trans (source_distance m))
    ((formula _ ⟨fuU, (f u).property⟩).symm.trans (source_distance u))
  have ratio_before : (m : ℝ) / (u : ℝ) < 1 :=
    (div_lt_one (show 0 < (u : ℝ) from positive.trans mu)).mpr mu
  exact lineMap_left_unique other source (P.faceCoordinates F (f u)) _ ratio_before.ne
    (candidate.symm.trans actual)

end SixVertexUnfolding.ConvexPolyhedron
