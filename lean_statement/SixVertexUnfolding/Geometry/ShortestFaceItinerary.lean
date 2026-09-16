import SixVertexUnfolding.Geometry.ShortestFaceSubdivision
import SixVertexUnfolding.Geometry.NonvertexFacetNeighborhoods

/-! A bounded ordered itinerary through whole original faces. Its size is
controlled by the number of facets, independently of the chosen shortest path. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set

variable {P : ConvexPolyhedron} {a b : Space}

/-- A finite chronological list of nonempty face portions. Repeated faces are allowed. -/
structure FaceItinerary (path : P.SurfacePath a b) where
  count : ℕ
  positive : 0 < count
  time : Fin (count + 1) → unitInterval
  increasing : StrictMono time
  first : time 0 = 0
  last : time (Fin.last count) = 1
  face : Fin count → P.Face
  inside : ∀ i, ∀ u ∈ Icc (time i.castSucc) (time i.succ), path.curve u ∈ (face i).val

/-- There are at most two face breakpoints per facet, in addition to the path endpoints. -/
theorem faceBreaks_card_le (path : P.SurfacePath a b) : path.faceBreaks.card ≤ 2 * Nat.card P.Face + 2 := by
  classical
  letI : Fintype P.Face := Fintype.ofFinite _
  have entry := Finset.card_image_le (f := path.faceEntry) (s := Finset.univ)
  have exit := Finset.card_image_le (f := path.faceExit) (s := Finset.univ)
  have middle := Finset.card_union_le (Finset.univ.image path.faceEntry) (Finset.univ.image path.faceExit)
  have all := Finset.card_union_le ({0, 1} : Finset unitInterval)
    (Finset.univ.image path.faceEntry ∪ Finset.univ.image path.faceExit)
  have endpoints : ({0, 1} : Finset unitInterval).card = 2 := by norm_num
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card] at entry exit
  change ({0, 1} ∪ (Finset.univ.image path.faceEntry ∪ Finset.univ.image path.faceExit)).card ≤ _
  omega

/-- Every finite shortest path has a uniformly bounded chronological face itinerary. -/
theorem exists_face_itinerary (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) :
    ∃ itinerary : path.FaceItinerary, itinerary.count ≤ 2 * Nat.card P.Face + 1 := by
  classical
  let times := path.faceBreaks
  have two : 2 ≤ times.card := by
    have subset : ({0, 1} : Finset unitInterval) ⊆ times := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      exacts [path.faceBreaks_endpoints.1, path.faceBreaks_endpoints.2]
    have bound := Finset.card_le_card subset
    norm_num at bound
    exact bound
  let n := times.card - 1
  have size : times.card = n + 1 := by dsimp [n]; omega
  let time : Fin (n + 1) ↪o unitInterval := times.orderEmbOfFin size
  have time_range : range time = (times : Set unitInterval) := times.range_orderEmbOfFin size
  have first : time 0 = 0 := by
    have in_range : (0 : unitInterval) ∈ range time := by rw [time_range]; exact path.faceBreaks_endpoints.1
    obtain ⟨i, hi⟩ := in_range
    exact le_antisymm (hi ▸ time.monotone (Fin.zero_le i)) unitInterval.nonneg'
  have last : time (Fin.last n) = 1 := by
    have in_range : (1 : unitInterval) ∈ range time := by rw [time_range]; exact path.faceBreaks_endpoints.2
    obtain ⟨i, hi⟩ := in_range
    exact le_antisymm unitInterval.le_one' (hi ▸ time.monotone (Fin.le_last i))
  have consecutive (i : Fin n) (u : unitInterval) (hu : u ∈ times) :
      u ∉ Ioo (time i.castSucc) (time i.succ) := by
    have in_range : u ∈ range time := by rw [time_range]; exact hu
    obtain ⟨j, rfl⟩ := in_range
    intro between
    have left := time.lt_iff_lt.mp between.1
    have right := time.lt_iff_lt.mp between.2
    change i.val < j.val at left
    change j.val < i.val + 1 at right
    omega
  choose face inside using fun i : Fin n => path.shortest_between_faceBreaks shortest finite
    (time i.castSucc) (time i.succ) (time.strictMono Fin.castSucc_lt_succ) (consecutive i)
  refine ⟨⟨n, by dsimp [n]; omega, time, time.strictMono, first, last, face, inside⟩, ?_⟩
  have bound := path.faceBreaks_card_le
  change times.card - 1 ≤ _
  dsimp [times] at *
  omega

namespace FaceItinerary

variable {path : P.SurfacePath a b} (itinerary : path.FaceItinerary)

/-- A meeting between successive nonempty portions lies at an interior parameter. -/
theorem crossing_is_interior (i j : Fin itinerary.count) (next : i.val + 1 = j.val) :
    0 < itinerary.time i.succ ∧ itinerary.time i.succ < 1 := by
  rw [← itinerary.first, ← itinerary.last]
  constructor
  · apply itinerary.increasing
    change 0 < i.val + 1
    omega
  · apply itinerary.increasing
    change i.val + 1 < itinerary.count
    omega

/-- Away from vertices, successive distinct faces share an original edge. -/
theorem successive_faces_adjacent
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices)
    (i j : Fin itinerary.count) (next : i.val + 1 = j.val) :
    itinerary.face i = itinerary.face j ∨ P.ShareEdge (itinerary.face i) (itinerary.face j) := by
  by_cases same : itinerary.face i = itinerary.face j
  · exact Or.inl same
  · apply Or.inr
    have same_time : i.succ = j.castSucc := Fin.ext next
    have increasing_i := itinerary.increasing.monotone (Fin.castSucc_le_succ i)
    have increasing_j := itinerary.increasing.monotone (Fin.castSucc_le_succ j)
    have left := itinerary.inside i (itinerary.time i.succ) ⟨increasing_i, le_rfl⟩
    have right := itinerary.inside j (itinerary.time j.castSucc) ⟨le_rfl, increasing_j⟩
    rw [← same_time] at right
    have interior := itinerary.crossing_is_interior i j next
    exact (itinerary.face i).shareEdge_of_common_nonvertex (itinerary.face j) same
      ⟨left, right⟩ (avoids _ interior.1 interior.2)

end FaceItinerary
end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
