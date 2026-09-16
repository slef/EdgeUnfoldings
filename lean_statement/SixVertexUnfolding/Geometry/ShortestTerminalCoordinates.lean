import SixVertexUnfolding.Geometry.ShortestNonbranching
import SixVertexUnfolding.Geometry.FacetCoordinateChange

/-! A local source-distance formula determines a shortest route near its
target. Global nonbranching then determines the whole route. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} {a b : Space}

/-- Two routes enter any target neighborhood at a common interior parameter. -/
theorem common_time_near_target (first second : P.SurfacePath a b) (U : Set Space)
    (openU : IsOpen U) (target : b ∈ U) :
    ∃ t : unitInterval, 0 < t ∧ t < 1 ∧ first.curve t ∈ U ∧ second.curve t ∈ U := by
  have first_near : ∀ᶠ t : ℝ in 𝓝 1, first.curve.extend t ∈ U :=
    first.curve.continuous_extend.continuousAt.eventually (openU.mem_nhds (by simpa using target))
  have second_near : ∀ᶠ t : ℝ in 𝓝 1, second.curve.extend t ∈ U :=
    second.curve.continuous_extend.continuousAt.eventually (openU.mem_nhds (by simpa using target))
  have positive : ∀ᶠ t : ℝ in 𝓝 1, 0 < t := Ioi_mem_nhds (by norm_num)
  obtain ⟨t, before, after, first_in, second_in⟩ := (positive.and (first_near.and second_near)).exists_lt
  let parameter : unitInterval := ⟨t, after.le, before.le⟩
  refine ⟨parameter, after, before, ?_, ?_⟩
  · simpa only [Path.extend_apply first.curve (show t ∈ Icc (0 : ℝ) 1 from parameter.property)] using first_in
  · simpa only [Path.extend_apply second.curve (show t ∈ Icc (0 : ℝ) 1 from parameter.property)] using second_in

/-- The local distance formula fixes the exact planar coordinate of each nearby route point. -/
theorem terminal_coordinate (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (F : P.Face) (target : b ∈ F.val) (source : Plane)
    (whole : P.surfaceDist a b = dist source (P.faceCoordinates F b))
    (t : unitInterval) (inside : path.curve t ∈ F.val)
    (at_t : P.surfaceDist a (path.curve t) = dist source (P.faceCoordinates F (path.curve t))) :
    P.faceCoordinates F (path.curve t) = AffineMap.lineMap source (P.faceCoordinates F b) (t : ℝ) := by
  have first : dist source (P.faceCoordinates F (path.curve t)) = path.length.toReal * (t : ℝ) := by
    rw [← at_t, path.source_distance shortest finite speed]
  have second : dist (P.faceCoordinates F (path.curve t)) (P.faceCoordinates F b) =
      path.length.toReal * (1 - (t : ℝ)) := by
    rw [P.faceCoordinates_rigid F _ inside b target, ← P.surfaceDist_eq_dist_in_face F inside target,
      path.target_distance shortest finite speed]
  have total : dist source (P.faceCoordinates F b) = path.length.toReal := by
    rw [← whole, surfaceDist, ← path.length_eq_surfaceEDist shortest]
  simpa only [sub_zero, div_one] using point_eq_lineMap_of_distance_ratios source
    (P.faceCoordinates F b) (P.faceCoordinates F (path.curve t)) 0 t 1 path.length.toReal
    (by norm_num) t.property.1 t.property.2 (by simpa using first) second (by simpa using total)

/-- A single local source-distance formula forces two vertex-free shortest routes to coincide. -/
theorem agree_of_terminal_distance_formula (first second : P.SurfacePath a b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → first.curve t ∉ P.vertices)
    (F : P.Face) (source : Plane) (U : Set Space) (openU : IsOpen U) (target : b ∈ U)
    (in_face : U ∩ frontier P.body ⊆ F.val)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x)) :
    ∀ t, first.curve t = second.curve t := by
  have boundary : b ∈ frontier P.body := first.curve.target ▸ first.on_surface 1
  have targetF := in_face ⟨target, boundary⟩
  have whole := formula b ⟨target, boundary⟩
  obtain ⟨t, positive, before_end, first_in, second_in⟩ := first.common_time_near_target second U openU target
  have firstF := in_face ⟨first_in, first.on_surface t⟩
  have secondF := in_face ⟨second_in, second.on_surface t⟩
  have left := first.terminal_coordinate first_shortest first_finite first_speed F targetF source whole t firstF
    (formula _ ⟨first_in, first.on_surface t⟩)
  have right := second.terminal_coordinate second_shortest second_finite second_speed F targetF source whole t secondF
    (formula _ ⟨second_in, second.on_surface t⟩)
  have meet : first.curve t = second.curve t := by
    apply dist_eq_zero.mp
    rw [← P.faceCoordinates_rigid F _ firstF _ secondF, left, right, dist_self]
  exact first.agree_of_interior_meeting second first_shortest second_shortest first_finite second_finite
    first_speed second_speed avoids t positive before_end meet

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
