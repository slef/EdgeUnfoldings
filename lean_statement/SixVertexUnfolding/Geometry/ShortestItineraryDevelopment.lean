import SixVertexUnfolding.Geometry.ShortestFaceItinerary
import SixVertexUnfolding.Geometry.FaceChainDevelopment
import SixVertexUnfolding.Geometry.ShortestHingeStraightness

/-! Coherent planar placements along a shortest path's itinerary. Every
intermediate crossing becomes straight in those same placements. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath.FaceItinerary

open Set

variable {P : ConvexPolyhedron} {a b : Space} {path : P.SurfacePath a b}
  (itinerary : path.FaceItinerary)

/-- Rigid outward placements along this chronological itinerary. -/
structure Development where
  place : Fin itinerary.count → Space →ᵃ[ℝ] Plane
  rigid : ∀ i, ∀ x ∈ (itinerary.face i).val, ∀ y ∈ (itinerary.face i).val,
    dist (place i x) (place i y) = dist x y
  joined : ∀ i j, i.val + 1 = j.val →
    EqOn (place i) (place j) ((itinerary.face i).val ∩ (itinerary.face j).val)
  outward : ∀ i j, i.val + 1 = j.val →
    OutwardFacePlacement (itinerary.face i) (itinerary.face j) (place i) (place j)

/-- Vertex avoidance ensures every transition uses an original edge or a repeated face. -/
theorem exists_development
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices) :
    Nonempty itinerary.Development := by
  obtain ⟨place, rigid, joined, outward⟩ := exists_ordered_face_development itinerary.positive
    itinerary.face (itinerary.successive_faces_adjacent avoids)
  exact ⟨⟨place, rigid, joined, outward⟩⟩

namespace Development

variable {itinerary} (net : itinerary.Development)

/-- Successive pieces meet at the same developed point. -/
theorem joined_at_crossing (i j : Fin itinerary.count) (next : i.val + 1 = j.val) :
    net.place i (path.curve (itinerary.time i.succ)) =
      net.place j (path.curve (itinerary.time j.castSucc)) := by
  have time_same : i.succ = j.castSucc := Fin.ext next
  have hi := itinerary.inside i (itinerary.time i.succ)
    ⟨itinerary.increasing.monotone (Fin.castSucc_le_succ i), le_rfl⟩
  have hj := itinerary.inside j (itinerary.time j.castSucc)
    ⟨le_rfl, itinerary.increasing.monotone (Fin.castSucc_le_succ j)⟩
  rw [← time_same] at hj ⊢
  exact net.joined i j next ⟨hi, hj⟩

/-- All crossings are straight simultaneously in the coherent chain development. -/
theorem crossing_straight (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices)
    (i j : Fin itinerary.count) (next : i.val + 1 = j.val) :
    Wbtw ℝ (net.place i (path.curve (itinerary.time i.castSucc)))
      (net.place i (path.curve (itinerary.time i.succ)))
      (net.place j (path.curve (itinerary.time j.succ))) := by
  let s := itinerary.time i.castSucc
  let m := itinerary.time i.succ
  let t := itinerary.time j.succ
  have same_time : i.succ = j.castSucc := Fin.ext next
  have sm : s ≤ m := itinerary.increasing.monotone (Fin.castSucc_le_succ i)
  have mt : m ≤ t := by
    change itinerary.time i.succ ≤ itinerary.time j.succ
    rw [same_time]
    exact itinerary.increasing.monotone (Fin.castSucc_le_succ j)
  have hs := itinerary.inside i s ⟨le_rfl, sm⟩
  have hm : path.curve m ∈ (itinerary.face i).val ∩ (itinerary.face j).val := by
    refine ⟨itinerary.inside i m ⟨sm, le_rfl⟩, ?_⟩
    apply itinerary.inside j m
    exact ⟨by rw [← same_time], mt⟩
  have ht := itinerary.inside j t ⟨by rw [← same_time]; exact mt, le_rfl⟩
  rcases itinerary.successive_faces_adjacent avoids i j next with same | shared
  · have ht_first : path.curve t ∈ (itinerary.face i).val := same ▸ ht
    have between := path.shortest_portion_range shortest finite (itinerary.face i) s t (sm.trans mt)
      hs ht_first m ⟨sm, mt⟩
    apply mem_segment_iff_wbtw.mp
    rw [← net.joined i j next ⟨ht_first, ht⟩, ← image_segment ℝ (net.place i)]
    exact ⟨path.curve m, between, rfl⟩
  · obtain ⟨p, p_vertex, q, q_vertex, pq, edge⟩ :=
      (itinerary.face i).shared_edge_endpoints (itinerary.face j) shared
    have hp : p ∈ (itinerary.face i).val ∩ (itinerary.face j).val := edge ▸ left_mem_segment ℝ p q
    have hq : q ∈ (itinerary.face i).val ∩ (itinerary.face j).val := edge ▸ right_mem_segment ℝ p q
    have middle := itinerary.crossing_is_interior i j next
    have nonvertex := avoids m middle.1 middle.2
    have inside : path.curve m ∈ openSegment ℝ p q := mem_openSegment_of_ne_left_right
      (fun equal => nonvertex (equal ▸ p_vertex)) (fun equal => nonvertex (equal ▸ q_vertex)) (edge ▸ hm)
    exact path.shortest_crossing_unfolds_straight shortest finite (itinerary.face i) (itinerary.face j)
      s m t sm mt hs hm ht p q pq hp hq inside (net.place i) (net.place j)
      (net.rigid i) (net.rigid j) (net.joined i j next)
      (net.outward i j next shared p ⟨hp, p_vertex⟩ q ⟨hq, q_vertex⟩ pq _ hs _ ht)

end Development
end SixVertexUnfolding.ConvexPolyhedron.SurfacePath.FaceItinerary
