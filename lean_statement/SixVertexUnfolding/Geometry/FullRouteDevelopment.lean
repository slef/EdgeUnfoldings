import SixVertexUnfolding.Geometry.ItineraryCoverage
import SixVertexUnfolding.Geometry.TerminalSourceData

/-! One bounded outward face development places the entire geodesic
on its straight radial segment, in the coordinates of its final face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The terminal source and every route point come from the same finite development. -/
theorem full_route_development (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) :
    ∃ code : P.FaceSequence,
      P.HasTerminalSource f (code.face code.last) (code.sourceImage (f 0)) ∧
      ∀ t : unitInterval, ∃ i : Fin code.count,
        (f t : Space) ∈ (code.face i).val ∧
        code.targetMotion (code.place i (f t)) = AffineMap.lineMap (code.sourceImage (f 0))
          (P.faceCoordinates (code.face code.last) (f 1)) (t : ℝ) := by
  let path := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  have avoids := graph.shortest_lipschitz_avoids_vertices small_faces path
    (fun h => different (Subtype.ext h)) shortest finite speed
  obtain ⟨itinerary, bounded⟩ := path.exists_face_itinerary shortest finite
  let code : P.FaceSequence := ⟨⟨⟨itinerary.count, by omega⟩, itinerary.face⟩,
    itinerary.positive, itinerary.successive_faces_adjacent avoids⟩
  let net : itinerary.Development := {
    place := code.place, rigid := code.rigid, joined := code.joined, outward := code.outward }
  have last_time : itinerary.time code.last.succ = 1 := by
    rw [show code.last.succ = Fin.last itinerary.count from Fin.ext (by
      dsimp [FaceSequence.last, FaceSequence.count, code]; have := itinerary.positive; omega)]
    exact itinerary.last
  have target : (f 1 : Space) ∈ (code.face code.last).val :=
    itinerary.inside code.last 1 ⟨unitInterval.le_one', last_time.ge⟩
  have developed (i : Fin itinerary.count) (t : unitInterval)
      (ht : t ∈ Icc (itinerary.time i.castSucc) (itinerary.time i.succ)) :
      code.targetMotion (code.place i (f t)) = AffineMap.lineMap (code.sourceImage (f 0))
        (P.faceCoordinates (code.face code.last) (f 1)) (t : ℝ) := by
    have straight := net.developed_route_is_segment shortest finite speed avoids i t ht
    change code.place i (f t) =
      AffineMap.lineMap (code.place code.first (f 0)) (code.place code.last (f 1)) (t : ℝ) at straight
    rw [straight, AffineMap.apply_lineMap, code.targetMotion_on_face _ target]
    rfl
  refine ⟨code, ?_, ?_⟩
  · refine ⟨itinerary.time code.last.castSucc, (itinerary.increasing Fin.castSucc_lt_succ).trans_eq last_time, ?_⟩
    intro t ht
    have interval : t ∈ Icc (itinerary.time code.last.castSucc) (itinerary.time code.last.succ) :=
      ⟨ht.1, ht.2.trans_eq last_time.symm⟩
    have contained := itinerary.inside code.last t interval
    change (f t : Space) ∈ (code.face code.last).val at contained
    refine ⟨contained, ?_⟩
    have coordinate := developed code.last t interval
    rwa [code.targetMotion_on_face _ contained] at coordinate
  · intro t
    obtain ⟨i, interval⟩ := itinerary.covers_time t
    exact ⟨i, itinerary.inside i t interval, developed i t interval⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
