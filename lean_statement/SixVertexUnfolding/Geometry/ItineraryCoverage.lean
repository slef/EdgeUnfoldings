import SixVertexUnfolding.Geometry.ShortestFaceItinerary

/-! Every route time belongs to at least one of its closed itinerary intervals. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath.FaceItinerary

open Set

variable {P : ConvexPolyhedron} {a b : Space} {path : P.SurfacePath a b} (itinerary : path.FaceItinerary)

/-- The finite chronological face portions cover the complete route parameter. -/
theorem covers_time (t : unitInterval) :
    ∃ i : Fin itinerary.count, t ∈ Icc (itinerary.time i.castSucc) (itinerary.time i.succ) := by
  by_contra missing
  have below : ∀ i : Fin (itinerary.count + 1), itinerary.time i ≤ t := by
    intro i
    induction i using Fin.induction with
    | zero => rw [itinerary.first]; exact t.property.1
    | succ i ih =>
        apply le_of_not_ge
        intro above
        exact missing ⟨i, ih, above⟩
  let last : Fin itinerary.count := ⟨itinerary.count - 1, by have := itinerary.positive; omega⟩
  have last_time : itinerary.time last.succ = 1 := by
    rw [show last.succ = Fin.last itinerary.count from Fin.ext (by
      dsimp [last]; have := itinerary.positive; omega)]
    exact itinerary.last
  exact missing ⟨last, below last.castSucc, by rw [last_time]; exact t.property.2⟩

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath.FaceItinerary
