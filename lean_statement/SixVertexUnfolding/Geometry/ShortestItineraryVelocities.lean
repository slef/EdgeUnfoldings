import SixVertexUnfolding.Geometry.ShortestItineraryDevelopment
import SixVertexUnfolding.Geometry.StraightChainVelocities
import SixVertexUnfolding.Geometry.IntrinsicSurfaceMetric

/-! Every developed face portion is affine at the original arc speed.
Straight crossings make all of their velocity vectors equal. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath.FaceItinerary.Development

open Set

variable {P : ConvexPolyhedron} {a b : Space} {path : P.SurfacePath a b}
  {itinerary : path.FaceItinerary} (net : itinerary.Development)

noncomputable def duration (i : Fin itinerary.count) : ℝ :=
  (itinerary.time i.succ : ℝ) - (itinerary.time i.castSucc : ℝ)

noncomputable def startPoint (i : Fin itinerary.count) : Plane :=
  net.place i (path.curve (itinerary.time i.castSucc))

noncomputable def endPoint (i : Fin itinerary.count) : Plane :=
  net.place i (path.curve (itinerary.time i.succ))

noncomputable def velocity (i : Fin itinerary.count) : Plane :=
  (duration i)⁻¹ • (net.endPoint i - net.startPoint i)

theorem duration_pos (i : Fin itinerary.count) : 0 < (duration i : ℝ) :=
  sub_pos.mpr (itinerary.increasing Fin.castSucc_lt_succ)

/-- The distance between two points in one placed portion is arc speed times elapsed time. -/
theorem piece_distance (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) (i : Fin itinerary.count)
    (s t : unitInterval) (hs : s ∈ Icc (itinerary.time i.castSucc) (itinerary.time i.succ))
    (ht : t ∈ Icc (itinerary.time i.castSucc) (itinerary.time i.succ)) :
    dist (net.place i (path.curve s)) (net.place i (path.curve t)) = path.length.toReal * dist s t := by
  rw [net.rigid i _ (itinerary.inside i s hs) _ (itinerary.inside i t ht),
    ← P.surfaceDist_eq_dist_in_face (itinerary.face i) (itinerary.inside i s hs) (itinerary.inside i t ht),
    path.surfaceDist_along shortest finite speed]

/-- Each straight face chord has the expected length. -/
theorem piece_length (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) (i : Fin itinerary.count) :
    dist (net.startPoint i) (net.endPoint i) = path.length.toReal * duration i := by
  have ordered := itinerary.increasing.monotone (Fin.castSucc_le_succ i)
  have distance := net.piece_distance shortest finite speed i (itinerary.time i.castSucc) (itinerary.time i.succ)
    ⟨le_rfl, ordered⟩ ⟨ordered, le_rfl⟩
  change dist (net.startPoint i) (net.endPoint i) = _ at distance
  rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] at distance
  change dist (net.startPoint i) (net.endPoint i) = path.length.toReal * |duration i| at distance
  rw [abs_of_nonneg (duration_pos i).le] at distance
  exact distance

/-- Every point of a face portion has its affine interpolation coordinate. -/
theorem piece_coordinates (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) (i : Fin itinerary.count)
    (u : unitInterval) (hu : u ∈ Icc (itinerary.time i.castSucc) (itinerary.time i.succ)) :
    net.place i (path.curve u) = net.startPoint i +
      ((u : ℝ) - (itinerary.time i.castSucc : ℝ)) • net.velocity i := by
  let s := itinerary.time i.castSucc
  let t := itinerary.time i.succ
  have ordered : s < t := itinerary.increasing Fin.castSucc_lt_succ
  have elapsed (v w : unitInterval) (vw : v ≤ w) : dist v w = (w : ℝ) - (v : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ w from vw))]
  have formula := point_eq_lineMap_of_distance_ratios (net.startPoint i) (net.endPoint i)
    (net.place i (path.curve u)) s u t path.length.toReal ordered hu.1 hu.2
    (by
      change dist (net.place i (path.curve s)) (net.place i (path.curve u)) = _
      rw [net.piece_distance shortest finite speed i s u ⟨le_rfl, ordered.le⟩ hu, elapsed s u hu.1])
    (by
      change dist (net.place i (path.curve u)) (net.place i (path.curve t)) = _
      rw [net.piece_distance shortest finite speed i u t hu ⟨ordered.le, le_rfl⟩, elapsed u t hu.2])
    (net.piece_length shortest finite speed i)
  rw [formula]
  simp only [AffineMap.lineMap_apply_module', velocity, duration, smul_smul, div_eq_mul_inv,
    s, t, add_comm]

/-- The two velocities on either side of a crossing are equal. -/
theorem successive_velocities_equal (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices)
    (i j : Fin itinerary.count) (next : i.val + 1 = j.val) : net.velocity i = net.velocity j := by
  have joined : net.endPoint i = net.startPoint j := net.joined_at_crossing i j next
  have straight : Wbtw ℝ (net.startPoint i) (net.endPoint i) (net.endPoint j) :=
    net.crossing_straight shortest finite avoids i j next
  have second := net.piece_length shortest finite speed j
  rw [← joined] at second
  have equal := straight_pieces_equal_velocity (net.startPoint i) (net.endPoint i) (net.endPoint j)
    (duration i) (duration j) path.length.toReal (duration_pos i) (duration_pos j)
    straight (net.piece_length shortest finite speed i) second
  simpa only [velocity, joined] using equal

/-- The complete finite development has one velocity vector. -/
theorem all_velocities_equal (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices) :
    ∀ i, net.velocity i = net.velocity ⟨0, itinerary.positive⟩ := by
  have all (k : ℕ) : ∀ i : Fin itinerary.count, i.val = k →
      net.velocity i = net.velocity ⟨0, itinerary.positive⟩ := by
    induction k with
    | zero =>
        intro i hi
        rw [show i = ⟨0, itinerary.positive⟩ from Fin.ext hi]
    | succ k ih =>
        intro i hi
        let j : Fin itinerary.count := ⟨k, by omega⟩
        exact (net.successive_velocities_equal shortest finite speed avoids j i (by dsimp [j]; omega)).symm.trans
          (ih j rfl)
  exact fun i => all i.val i rfl

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath.FaceItinerary.Development
