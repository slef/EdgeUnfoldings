import SixVertexUnfolding.Geometry.VertexFanFigure
import SixVertexUnfolding.Geometry.FourRayPerimeter
import SixVertexUnfolding.Geometry.FiveRayPerimeter

/-! The actual surface angle is strictly below a full turn at every
vertex of the small polyhedra, including degrees three, four, and five. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set Real InnerProductGeometry

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)

noncomputable def sectorAngle (i : Fin n) : ℝ :=
  EuclideanGeometry.angle (fan.neighbor i : Space) pole (fan.neighbor (i + 1))

noncomputable def totalAngle : ℝ := ∑ i : Fin n, fan.sectorAngle i

theorem sectorAngle_pos (i : Fin n) : 0 < fan.sectorAngle i :=
  EuclideanGeometry.angle_pos_of_not_collinear (fan.triangle_noncollinear i)

theorem sectorAngle_lt_pi (i : Fin n) : fan.sectorAngle i < π :=
  EuclideanGeometry.angle_lt_pi_of_not_collinear (fan.triangle_noncollinear i)

include fan in
theorem sector_count_bounds (size : P.vertices.card ≤ 6) : 3 ≤ n ∧ n ≤ 5 := by
  classical
  have count := Nat.card_congr fan.order
  rw [Nat.card_fin] at count
  have lower := P.edgeGraph_min_degree pole
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at lower
  have upper := Fintype.card_lt_of_injective_of_notMem
    (fun v : P.edgeGraph.neighborSet pole => v.val) Subtype.val_injective
    (b := pole) (by
      rintro ⟨v, same⟩
      have edge : P.edgeGraph.Adj pole v.val := v.property
      exact edge.ne same.symm)
  have vertex_count : Fintype.card P.Vertex = P.vertices.card := by simp [Vertex]
  rw [← Nat.card_eq_fintype_card, vertex_count] at upper
  omega

/-- The three- and four-ray bounds and the five-ray bound cover every possible degree. -/
theorem totalAngle_lt_two_pi (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) : fan.totalAngle < 2 * π := by
  obtain ⟨normal, strict⟩ := P.vertex_strict_support pole.property
  let figure : P.VertexFigure pole := ⟨normal, strict⟩
  let height := -(innerSL ℝ figure.normal).toLinearMap
  have levels (i : Fin n) : height (fan.ray figure i) = 1 := fan.ray_height figure i
  have actual : fan.totalAngle = ∑ i : Fin n,
      angle (fan.ray figure i) (fan.ray figure (i + 1)) := by
    simp only [totalAngle, sectorAngle, fan.ray_angle]
  rw [actual]
  have counts := fan.sector_count_bounds size
  have cases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases cases with rfl | rfl | rfl
  · have bound := spherical_triangle_perimeter_lt height
      (fan.ray figure 0) (fan.ray figure 1) (fan.ray figure 2)
      (by rw [levels]; norm_num) (by rw [levels]; norm_num) (by rw [levels]; norm_num)
    simpa [Fin.sum_univ_succ, add_assoc] using bound
  · choose side nonzero left right bounds _ using fan.ray_side_exists figure small_faces
    let supported : FourRayFan := {
      ray := fan.ray figure
      distinct := fan.ray_injective figure
      height := height
      level := levels
      spans := fan.rays_span figure
      side := side
      side_nonzero := nonzero
      side_left := left
      side_right := right
      side_bound := bounds }
    exact supported.sum_angles_lt_two_pi
  · choose side nonzero left right bounds strict_sides using fan.ray_side_exists figure small_faces
    let supported : FiveRayFan := {
      ray := fan.ray figure
      distinct := fan.ray_injective figure
      height := height
      level := levels
      spans := fan.rays_span figure
      side := side
      side_nonzero := nonzero
      side_left := left
      side_right := right
      side_bound := bounds
      side_strict := strict_sides }
    exact supported.sum_angles_lt_two_pi

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
