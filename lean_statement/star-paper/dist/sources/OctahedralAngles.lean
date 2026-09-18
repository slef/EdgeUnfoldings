import SixVertexUnfolding.Geometry.OctahedralSubdivision

/-! Actual spatial triangle angles and their six-vertex total curvature identity. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles EuclideanGeometry

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- The ordinary spatial angle at a named corner of a subdivision triangle. -/
noncomputable def cornerAngle (t : Fin 8) (i : Fin 3) : ℝ :=
  angle (graph.trianglePoint t (i + 1)) (graph.trianglePoint t i) (graph.trianglePoint t (i + 2))

/-- The sum of the incident subdivision angles at one original vertex. -/
noncomputable def totalAngleAt (v : Fin 6) : ℝ :=
  ∑ t : Fin 8, ∑ i : Fin 3, if corner t i = v then graph.cornerAngle t i else 0

/-- Curvature is the angular deficit at this genuine original vertex. -/
noncomputable def curvature (v : Fin 6) : ℝ := 2 * Real.pi - graph.totalAngleAt v

/-- The three cyclically ordered corners remain noncollinear. -/
theorem corner_triangle_not_collinear (t : Fin 8) (i : Fin 3) :
    ¬ Collinear ℝ ({graph.trianglePoint t (i + 1), graph.trianglePoint t i,
      graph.trianglePoint t (i + 2)} : Set Space) := by
  apply P.no_three_collinear_vertices
    (graph.vertex (corner t (i + 1))).property (graph.vertex (corner t i)).property
    (graph.vertex (corner t (i + 2))).property
  · exact (graph.trianglePoint_injective t).ne ((by decide : ∀ i : Fin 3, i + 1 ≠ i) i)
  · exact (graph.trianglePoint_injective t).ne ((by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i)
  · exact (graph.trianglePoint_injective t).ne ((by decide : ∀ i : Fin 3, i ≠ i + 2) i)

theorem cornerAngle_pos (t : Fin 8) (i : Fin 3) : 0 < graph.cornerAngle t i :=
  angle_pos_of_not_collinear (graph.corner_triangle_not_collinear t i)

theorem cornerAngle_lt_pi (t : Fin 8) (i : Fin 3) : graph.cornerAngle t i < Real.pi :=
  angle_lt_pi_of_not_collinear (graph.corner_triangle_not_collinear t i)

/-- Each actual subdivision triangle contributes exactly pi in angle sum. -/
theorem sum_cornerAngle (t : Fin 8) : ∑ i : Fin 3, graph.cornerAngle t i = Real.pi := by
  have total := angle_add_angle_add_angle_eq_pi (graph.trianglePoint t 2)
    ((graph.trianglePoint_injective t).ne (by decide : (1 : Fin 3) ≠ 0))
  simp only [Fin.sum_univ_three, cornerAngle]
  change angle (graph.trianglePoint t 1) (graph.trianglePoint t 0) (graph.trianglePoint t 2) +
    angle (graph.trianglePoint t 2) (graph.trianglePoint t 1) (graph.trianglePoint t 0) +
    angle (graph.trianglePoint t 0) (graph.trianglePoint t 2) (graph.trianglePoint t 1) = Real.pi
  rw [angle_comm (graph.trianglePoint t 1) (graph.trianglePoint t 0),
    angle_comm (graph.trianglePoint t 2) (graph.trianglePoint t 1),
    angle_comm (graph.trianglePoint t 0) (graph.trianglePoint t 2)]
  linarith

/-- The 24 corner angles are counted exactly once across the six original vertices. -/
theorem sum_totalAngleAt : ∑ v : Fin 6, graph.totalAngleAt v = 8 * Real.pi := by
  unfold totalAngleAt
  calc
    (∑ v : Fin 6, ∑ t : Fin 8, ∑ i : Fin 3, if corner t i = v then graph.cornerAngle t i else 0) =
        ∑ t : Fin 8, ∑ i : Fin 3, ∑ v : Fin 6, if corner t i = v then graph.cornerAngle t i else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t member
      rw [Finset.sum_comm]
    _ = ∑ t : Fin 8, ∑ i : Fin 3, graph.cornerAngle t i := by simp
    _ = 8 * Real.pi := by simp [graph.sum_cornerAngle]

/-- Gauss--Bonnet for this explicit six-vertex subdivision, derived from its actual spatial angles. -/
theorem sum_curvature : ∑ v : Fin 6, graph.curvature v = 4 * Real.pi := by
  simp only [curvature, Finset.sum_sub_distrib, graph.sum_totalAngleAt]
  norm_num
  ring

/-- Every vertex has a positive incident angle sum. -/
theorem totalAngleAt_pos (v : Fin 6) : 0 < graph.totalAngleAt v := by
  obtain ⟨t, i, at_vertex⟩ := (by decide : ∀ v : Fin 6, ∃ t : Fin 8, ∃ i : Fin 3, corner t i = v) v
  have nonnegative (t : Fin 8) (i : Fin 3) : 0 ≤ if corner t i = v then graph.cornerAngle t i else 0 := by
    split_ifs
    · exact (graph.cornerAngle_pos t i).le
    · exact le_rfl
  apply Finset.sum_pos' (fun t _ => Finset.sum_nonneg (fun i _ => nonnegative t i))
  refine ⟨t, Finset.mem_univ _, ?_⟩
  apply Finset.sum_pos' (fun i _ => nonnegative t i)
  exact ⟨i, Finset.mem_univ _, by rw [if_pos at_vertex]; exact graph.cornerAngle_pos t i⟩

/-- The upper curvature bound follows from nondegenerate actual face angles. -/
theorem curvature_lt_two_pi (v : Fin 6) : graph.curvature v < 2 * Real.pi := by
  have positive := graph.totalAngleAt_pos v
  unfold curvature
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
