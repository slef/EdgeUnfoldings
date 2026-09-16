import SixVertexUnfolding.Geometry.ShortestItineraryVelocities

/-! A shortest route develops to one affine planar line across its entire
finite face itinerary, with its actual arc length as constant speed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath.FaceItinerary.Development

open Set

variable {P : ConvexPolyhedron} {a b : Space} {path : P.SurfacePath a b}
  {itinerary : path.FaceItinerary} (net : itinerary.Development)

/-- The first index in the nonempty itinerary. -/
def firstIndex : Fin itinerary.count := ⟨0, itinerary.positive⟩

/-- The last index in the nonempty itinerary. -/
def lastIndex : Fin itinerary.count := ⟨itinerary.count - 1, by have := itinerary.positive; omega⟩

/-- Each developed endpoint is start plus duration times velocity. -/
theorem endPoint_eq_start_add_velocity (i : Fin itinerary.count) :
    net.endPoint i = net.startPoint i + duration i • net.velocity i := by
  rw [velocity, smul_smul, mul_inv_cancel₀ (duration_pos i).ne', one_smul]
  module

/-- No positional jump accumulates as the common velocity passes through the face chain. -/
theorem all_startPoints_on_line (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices) :
    ∀ i, net.startPoint i = net.startPoint firstIndex +
      (itinerary.time i.castSucc : ℝ) • net.velocity firstIndex := by
  have velocities := net.all_velocities_equal shortest finite speed avoids
  have ends (i : Fin itinerary.count) : net.endPoint i = net.startPoint i + duration i • net.velocity firstIndex := by
    rw [net.endPoint_eq_start_add_velocity, velocities i]
    rfl
  have all (k : ℕ) : ∀ i : Fin itinerary.count, i.val = k →
      net.startPoint i = net.startPoint firstIndex + (itinerary.time i.castSucc : ℝ) • net.velocity firstIndex := by
    induction k with
    | zero =>
        intro i hi
        have equal : i = firstIndex := Fin.ext hi
        rw [equal]
        change net.startPoint firstIndex = net.startPoint firstIndex + (itinerary.time 0 : ℝ) • _
        rw [itinerary.first]
        simp
    | succ k ih =>
        intro i hi
        let j : Fin itinerary.count := ⟨k, by omega⟩
        have next : j.val + 1 = i.val := by dsimp [j]; omega
        have joined : net.endPoint j = net.startPoint i := net.joined_at_crossing j i next
        have same_time : i.castSucc = j.succ := Fin.ext next.symm
        rw [← joined, ends j, ih j rfl, same_time]
        simp only [duration]
        module
  exact fun i => all i.val i rfl

/-- The complete developed route has a single affine formula in its original parameter. -/
theorem global_coordinates (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices)
    (i : Fin itinerary.count) (u : unitInterval)
    (hu : u ∈ Icc (itinerary.time i.castSucc) (itinerary.time i.succ)) :
    net.place i (path.curve u) = net.startPoint firstIndex + (u : ℝ) • net.velocity firstIndex := by
  rw [net.piece_coordinates shortest finite speed i u hu,
    net.all_startPoints_on_line shortest finite speed avoids i,
    net.all_velocities_equal shortest finite speed avoids i]
  dsimp only [firstIndex]
  module

/-- The common developed velocity has norm exactly equal to the surface path's length. -/
theorem velocity_norm (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) (i : Fin itinerary.count) :
    ‖net.velocity i‖ = path.length.toReal := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (duration_pos i)),
    ← dist_eq_norm, dist_comm, net.piece_length shortest finite speed i]
  field_simp [(duration_pos i).ne']

/-- The source placement is the first point of the developed line. -/
theorem source_on_line : net.place firstIndex a = net.startPoint firstIndex := by
  change _ = net.place firstIndex (path.curve (itinerary.time 0))
  rw [itinerary.first, path.curve.source]

/-- The target placement is one full velocity vector beyond the source. -/
theorem target_on_line (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices) :
    net.place lastIndex b = net.startPoint firstIndex + net.velocity firstIndex := by
  have last_time : itinerary.time (lastIndex (itinerary := itinerary)).succ = 1 := by
    rw [show (lastIndex (itinerary := itinerary)).succ = Fin.last itinerary.count from Fin.ext (by
      dsimp [lastIndex]; have := itinerary.positive; omega)]
    exact itinerary.last
  have formula := net.global_coordinates shortest finite speed avoids lastIndex 1
    ⟨unitInterval.le_one', by rw [last_time]⟩
  simpa only [path.curve.target, show ((1 : unitInterval) : ℝ) = 1 from rfl, one_smul] using formula

/-- The endpoint chord of the coherent development is the whole intrinsic path length. -/
theorem developed_chord_length (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices) :
    dist (net.place firstIndex a) (net.place lastIndex b) = path.length.toReal := by
  rw [net.source_on_line, net.target_on_line shortest finite speed avoids, dist_eq_norm]
  simpa only [sub_add_cancel_left, norm_neg] using net.velocity_norm shortest finite speed firstIndex

/-- Each placed face portion lies on the single segment between the developed endpoints. -/
theorem developed_route_is_segment (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices)
    (i : Fin itinerary.count) (u : unitInterval)
    (hu : u ∈ Icc (itinerary.time i.castSucc) (itinerary.time i.succ)) :
    net.place i (path.curve u) = AffineMap.lineMap (net.place firstIndex a) (net.place lastIndex b) (u : ℝ) := by
  rw [net.global_coordinates shortest finite speed avoids i u hu, net.source_on_line,
    net.target_on_line shortest finite speed avoids, AffineMap.lineMap_apply_module']
  simp only [add_sub_cancel_left, add_comm]

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath.FaceItinerary.Development
