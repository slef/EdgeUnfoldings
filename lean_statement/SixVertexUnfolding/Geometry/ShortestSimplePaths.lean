import SixVertexUnfolding.Geometry.ShortestFaceSubdivision

/-! Shortest paths between distinct boundary points can be chosen without
pauses or self-intersections. Their arc length is proportional to elapsed time. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set
open scoped ENNReal NNReal

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b : Space}

/-- Speed times elapsed time bounds the length of a portion. -/
theorem portion_length_le_of_lipschitz (path : P.SurfacePath a b) {C : ℝ≥0}
    (speed : LipschitzWith C path.curve) (s t : unitInterval) (ordered : s ≤ t) :
    (path.portion s t ordered).length ≤ ENNReal.ofReal (C * ((t : ℝ) - (s : ℝ))) := by
  have parameter_length : eVariationOn (id : unitInterval → unitInterval) (Icc s t) ≤
      ENNReal.ofReal ((t : ℝ) - (s : ℝ)) := by
    have monotone : MonotoneOn ((↑) : unitInterval → ℝ) Set.univ := fun _ _ _ _ h => h
    simpa only [univ_inter] using monotone.eVariationOn_le (mem_univ s) (mem_univ t)
  have bound := speed.lipschitzOnWith.comp_eVariationOn_le
    (show MapsTo (id : unitInterval → unitInterval) (Icc s t) Set.univ from fun _ _ => mem_univ _)
  rw [portion_length]
  refine bound.trans ?_
  rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  exact mul_le_mul_right parameter_length (C : ℝ≥0∞)

/-- A path traversed with its total length as speed bound has exactly constant arc speed. -/
theorem portion_length_constant_speed (path : P.SurfacePath a b) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve)
    (s t : unitInterval) (ordered : s ≤ t) :
    (path.portion s t ordered).length.toReal = path.length.toReal * ((t : ℝ) - (s : ℝ)) := by
  have bound (u v : unitInterval) (huv : u ≤ v) :
      (path.portion u v huv).length.toReal ≤ path.length.toReal * ((v : ℝ) - (u : ℝ)) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (path.portion_length_le_of_lipschitz speed u v huv)
    simpa only [ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr huv)),
      ENNReal.coe_toNNReal_eq_toReal] using h
  have left := bound 0 s unitInterval.nonneg'
  have middle := bound s t ordered
  have right := bound t 1 unitInterval.le_one'
  have split := congrArg ENNReal.toReal (path.length_split_three s t ordered)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨path.portion_finite finite _ _ _, path.portion_finite finite _ _ _⟩)
    (path.portion_finite finite _ _ _),
    ENNReal.toReal_add (path.portion_finite finite _ _ _) (path.portion_finite finite _ _ _)] at split
  change (path.portion 0 s _).length.toReal ≤ path.length.toReal * ((s : ℝ) - 0) at left
  change (path.portion t 1 _).length.toReal ≤ path.length.toReal * (1 - (t : ℝ)) at right
  nlinarith

/-- A constant-speed shortest route between distinct points has no self-intersection. -/
theorem shortest_lipschitz_injective (path : P.SurfacePath a b) (different : a ≠ b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) : Function.Injective path.curve := by
  have positive : 0 < path.length.toReal := ENNReal.toReal_pos (by
    intro zero
    have := path.chord_le_length
    rw [zero] at this
    exact different (edist_eq_zero.mp (le_antisymm this bot_le))) finite
  intro s t equal
  wlog ordered : s ≤ t generalizing s t
  · exact (this equal.symm (le_of_not_ge ordered)).symm
  obtain ⟨F, hs⟩ := P.boundary_point_in_face (path.on_surface s)
  have ht : path.curve t ∈ F.val := equal ▸ hs
  have zero := (path.portion s t ordered).shortest_cofacial_length
    (path.portion_shortest shortest finite s t ordered) F hs ht
  rw [edist_eq_zero.mpr equal] at zero
  have length := path.portion_length_constant_speed finite speed s t ordered
  rw [zero, ENNReal.toReal_zero] at length
  apply Subtype.ext
  have : (t : ℝ) - (s : ℝ) = 0 := (mul_eq_zero.mp length.symm).resolve_left (ne_of_gt positive)
  linarith

end SurfacePath

/-- Distinct boundary points admit a simple, finite shortest route, with constant arc speed. -/
theorem exists_simple_shortest_surface_path (P : ConvexPolyhedron) {a b : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) (different : a ≠ b) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve ∧ Function.Injective path.curve := by
  obtain ⟨path, shortest, finite, speed⟩ := P.exists_shortest_lipschitz_surface_path ha hb
  exact ⟨path, shortest, finite, speed,
    path.shortest_lipschitz_injective different shortest finite speed⟩

end SixVertexUnfolding.ConvexPolyhedron
