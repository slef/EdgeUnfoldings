import SixVertexUnfolding.Geometry.ShortestSourceImages

/-! Each shortest route has a terminal face and a fixed developed source
copy that determine its whole final straight portion. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set

variable {P : ConvexPolyhedron} {a b : Space}

/-- One bounded face sequence determines the exact terminal coordinates of the route. -/
theorem exists_terminal_source_code (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices) :
    ∃ code : P.FaceSequence, ∃ start : unitInterval, start < 1 ∧
      ∀ t ∈ Icc start 1, path.curve t ∈ (code.face code.last).val ∧
        P.faceCoordinates (code.face code.last) (path.curve t) =
          AffineMap.lineMap (code.sourceImage a) (P.faceCoordinates (code.face code.last) b) (t : ℝ) := by
  obtain ⟨itinerary, bounded⟩ := path.exists_face_itinerary shortest finite
  let code : P.FaceSequence := ⟨⟨⟨itinerary.count, by omega⟩, itinerary.face⟩,
    itinerary.positive, itinerary.successive_faces_adjacent avoids⟩
  let net : itinerary.Development := {
    place := code.place, rigid := code.rigid, joined := code.joined, outward := code.outward }
  have last_time : itinerary.time code.last.succ = 1 := by
    rw [show code.last.succ = Fin.last itinerary.count from Fin.ext (by
      dsimp [FaceSequence.last, FaceSequence.count, code]; have := itinerary.positive; omega)]
    exact itinerary.last
  have target := itinerary.inside code.last 1 ⟨unitInterval.le_one', last_time.ge⟩
  rw [path.curve.target] at target
  refine ⟨code, itinerary.time code.last.castSucc, ?_, ?_⟩
  · exact (itinerary.increasing Fin.castSucc_lt_succ).trans_eq last_time
  · intro t ht
    have interval : t ∈ Icc (itinerary.time code.last.castSucc) (itinerary.time code.last.succ) :=
      ⟨ht.1, ht.2.trans_eq last_time.symm⟩
    have on_face := itinerary.inside code.last t interval
    refine ⟨on_face, ?_⟩
    rw [← code.targetMotion_on_face _ on_face]
    have straight := net.developed_route_is_segment shortest finite speed avoids code.last t interval
    change code.place code.last (path.curve t) =
      AffineMap.lineMap (code.place code.first a) (code.place code.last b) (t : ℝ) at straight
    rw [straight, AffineMap.apply_lineMap, code.targetMotion_on_face b target]
    rfl

/-- A common terminal source code determines the whole vertex-free shortest route. -/
theorem agree_of_terminal_source_code (first second : P.SurfacePath a b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → first.curve t ∉ P.vertices)
    (code : P.FaceSequence) (s u : unitInterval) (s_before : s < 1) (u_before : u < 1)
    (first_tail : ∀ t ∈ Icc s 1, first.curve t ∈ (code.face code.last).val ∧
      P.faceCoordinates (code.face code.last) (first.curve t) =
        AffineMap.lineMap (code.sourceImage a) (P.faceCoordinates (code.face code.last) b) (t : ℝ))
    (second_tail : ∀ t ∈ Icc u 1, second.curve t ∈ (code.face code.last).val ∧
      P.faceCoordinates (code.face code.last) (second.curve t) =
        AffineMap.lineMap (code.sourceImage a) (P.faceCoordinates (code.face code.last) b) (t : ℝ)) :
    ∀ t, first.curve t = second.curve t := by
  obtain ⟨t, after, before⟩ := exists_between (max_lt s_before u_before)
  have positive : 0 < t := unitInterval.nonneg'.trans_lt ((le_max_left s u).trans_lt after)
  have left := first_tail t ⟨(le_max_left s u).trans after.le, before.le⟩
  have right := second_tail t ⟨(le_max_right s u).trans after.le, before.le⟩
  have meet : first.curve t = second.curve t := by
    apply dist_eq_zero.mp
    rw [← P.faceCoordinates_rigid (code.face code.last) _ left.1 _ right.1, left.2, right.2, dist_self]
  exact first.agree_of_interior_meeting second first_shortest second_shortest first_finite second_finite
    first_speed second_speed avoids t positive before meet

/-- Pointwise equality of the curves is equality of the surface paths. -/
theorem eq_of_curve_eq (first second : P.SurfacePath a b) (same : ∀ t, first.curve t = second.curve t) :
    first = second := by
  have curves : first.curve = second.curve := Path.ext (funext same)
  cases first
  cases second
  cases curves
  rfl

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
