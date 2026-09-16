import SixVertexUnfolding.Geometry.JoinedTriangles

/-! Closed triangles are exactly the three closed half-planes to the left of their oriented edges. -/

namespace SixVertexUnfolding

/-- Signed area is preserved by cycling the three triangle vertices. -/
theorem triangle_area_cycle (a b c : Plane) : det (c - b) (a - b) = det (b - a) (c - a) := by
  simp only [det, PiLp.sub_apply]
  ring

/-- Every point of a positively oriented triangle is on its base's closed left side. -/
theorem triangle_base_height_nonneg (a b c x : Plane)
    (positive : 0 ≤ det (b - a) (c - a)) (member : x ∈ convexHull ℝ ({a, b, c} : Set Plane)) :
    0 ≤ det (b - a) (x - a) := by
  obtain ⟨s, t, u, _, _, hu, total, expression⟩ := triangle_weights a b c x member
  rw [triangle_weighted_area a b c x s t u total expression]
  exact mul_nonneg hu positive

/-- Three oriented edge-side inequalities give membership in the actual translated triangle. -/
theorem triangle_mem_of_edge_sides (a b c x : Plane) (positive : 0 < det (b - a) (c - a))
    (ab : 0 ≤ det (b - a) (x - a)) (bc : 0 ≤ det (c - b) (x - b))
    (ca : 0 ≤ det (a - c) (x - c)) : x ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
  have relative : x - a ∈ convexHull ℝ ({0, b - a, c - a} : Set Plane) := by
    apply triangle_mem_of_three_halfplanes (b - a) (c - a) (x - a) positive ab
    · have same : det (x - a) (c - a) = det (a - c) (x - c) := by
        simp only [det, PiLp.sub_apply]; ring
      rwa [same]
    · simpa only [sub_sub_sub_cancel_right] using bc
  obtain ⟨s, t, u, hs, ht, hu, total, expression⟩ := triangle_weights 0 (b - a) (c - a) (x - a) relative
  apply triangle_mem_of_weights a b c x s t u hs ht hu total
  have shifted : x = a + (s • 0 + t • (b - a) + u • (c - a)) := by rw [expression]; module
  rw [shifted, show s = 1 - t - u by linarith]
  module

/-- The complete closed half-plane description, including all three edges. -/
theorem triangle_mem_iff_edge_sides (a b c x : Plane) (positive : 0 < det (b - a) (c - a)) :
    x ∈ convexHull ℝ ({a, b, c} : Set Plane) ↔
      0 ≤ det (b - a) (x - a) ∧ 0 ≤ det (c - b) (x - b) ∧ 0 ≤ det (a - c) (x - c) := by
  constructor
  · intro member
    have rotated : x ∈ convexHull ℝ ({b, c, a} : Set Plane) := by
      convert member using 1
      congr 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have rotated' : x ∈ convexHull ℝ ({c, a, b} : Set Plane) := by
      convert member using 1
      congr 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact ⟨triangle_base_height_nonneg a b c x positive.le member,
      triangle_base_height_nonneg b c a x (by rw [triangle_area_cycle]; exact positive.le) rotated,
      triangle_base_height_nonneg c a b x (by rw [triangle_area_cycle, triangle_area_cycle]; exact positive.le) rotated'⟩
  · rintro ⟨ab, bc, ca⟩
    exact triangle_mem_of_edge_sides a b c x positive ab bc ca

/-- Strict edge inequalities give ordinary planar interior, by continuity of all three heights. -/
theorem triangle_interior_of_strict_edge_sides (a b c x : Plane) (positive : 0 < det (b - a) (c - a))
    (ab : 0 < det (b - a) (x - a)) (bc : 0 < det (c - b) (x - b))
    (ca : 0 < det (a - c) (x - c)) : x ∈ interior (convexHull ℝ ({a, b, c} : Set Plane)) := by
  let u : Set Plane := {y | 0 < det (b - a) (y - a) ∧ 0 < det (c - b) (y - b) ∧ 0 < det (a - c) (y - c)}
  have height_continuous (v origin : Plane) : Continuous (fun y : Plane => det v (y - origin)) :=
    (detHeight v).continuous.comp (continuous_id.sub continuous_const)
  have open_u : IsOpen u := (isOpen_lt continuous_const (height_continuous _ _)).inter
    ((isOpen_lt continuous_const (height_continuous _ _)).inter (isOpen_lt continuous_const (height_continuous _ _)))
  exact mem_interior.mpr ⟨u, fun y h => triangle_mem_of_edge_sides a b c y positive h.1.le h.2.1.le h.2.2.le,
    open_u, ⟨ab, bc, ca⟩⟩

end SixVertexUnfolding
