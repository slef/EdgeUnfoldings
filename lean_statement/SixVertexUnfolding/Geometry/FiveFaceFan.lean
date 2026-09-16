import SixVertexUnfolding.Geometry.UniversalVertexCurvature

/-! The five actual faces around the remaining degree-five vertex.
The constructor below supplies every field from the convex polyhedron. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set EuclideanGeometry Real

/-- A cyclic list of the five original triangular faces at one vertex. -/
structure FiveFaceFan (P : ConvexPolyhedron) (pole : P.Vertex) where
  neighbor : Fin 5 → P.Vertex
  distinct : Function.Injective neighbor
  not_pole : ∀ i, neighbor i ≠ pole
  face : Fin 5 → P.Face
  face_vertices : ∀ i, (face i).val ∩ (P.vertices : Set Space) =
    {(pole : Space), (neighbor i : Space), (neighbor (i + 1) : Space)}
  covers : ∀ F : P.Face, (pole : Space) ∈ F.val ↔ F ∈ range face
  angle_bound : (∑ i : Fin 5, angle (neighbor i : Space) pole (neighbor (i + 1))) < 2 * π

/-- A universal vertex in the remaining six-vertex cases supplies the complete fan. -/
theorem exists_universal_five_face_fan (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (pole : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ pole → P.edgeGraph.Adj pole v) :
    Nonempty (P.FiveFaceFan pole) := by
  obtain ⟨order, faces, vertices, covers, deficit⟩ :=
    P.universal_vertex_angle_deficit size small_faces pole universal
  exact ⟨{
    neighbor := fun i => (order i).val
    distinct := fun _ _ same => order.injective (Subtype.ext same)
    not_pole := fun i => (order i).property
    face := faces
    face_vertices := vertices
    covers := covers
    angle_bound := deficit }⟩

namespace FiveFaceFan

variable {P : ConvexPolyhedron} {pole : P.Vertex} (fan : P.FiveFaceFan pole)

def triangle (i : Fin 5) : Set Space :=
  convexHull ℝ ({(pole : Space), (fan.neighbor i : Space), (fan.neighbor (i + 1) : Space)} : Set Space)

theorem triangle_eq_face (i : Fin 5) : fan.triangle i = (fan.face i).val := by
  rw [(fan.face i).eq_convexHull_vertices, fan.face_vertices]
  rfl

theorem pole_mem_face (i : Fin 5) : (pole : Space) ∈ (fan.face i).val := by
  rw [← fan.triangle_eq_face]
  exact subset_convexHull ℝ _ (by simp)

theorem left_mem_face (i : Fin 5) : (fan.neighbor i : Space) ∈ (fan.face i).val := by
  rw [← fan.triangle_eq_face]
  exact subset_convexHull ℝ _ (by simp)

theorem right_mem_face (i : Fin 5) : (fan.neighbor (i + 1) : Space) ∈ (fan.face i).val := by
  rw [← fan.triangle_eq_face]
  exact subset_convexHull ℝ _ (by simp)

theorem neighbor_ne_pole (i : Fin 5) : (fan.neighbor i : Space) ≠ pole :=
  fun same => fan.not_pole i (Subtype.ext same)

theorem triangle_noncollinear (i : Fin 5) :
    ¬ Collinear ℝ ({(fan.neighbor i : Space), (pole : Space),
      (fan.neighbor (i + 1) : Space)} : Set Space) := by
  apply P.no_three_collinear_vertices (fan.neighbor i).property pole.property
    (fan.neighbor (i + 1)).property (fan.neighbor_ne_pole i)
  · intro same
    exact (by decide : ∀ i : Fin 5, i ≠ i + 1) i (fan.distinct (Subtype.ext same))
  · exact (fan.neighbor_ne_pole (i + 1)).symm

noncomputable def sectorAngle (i : Fin 5) : ℝ :=
  angle (fan.neighbor i : Space) pole (fan.neighbor (i + 1))

noncomputable def totalAngle : ℝ := ∑ i : Fin 5, fan.sectorAngle i

theorem sectorAngle_pos (i : Fin 5) : 0 < fan.sectorAngle i :=
  angle_pos_of_not_collinear (fan.triangle_noncollinear i)

theorem sectorAngle_lt_pi (i : Fin 5) : fan.sectorAngle i < π :=
  angle_lt_pi_of_not_collinear (fan.triangle_noncollinear i)

theorem totalAngle_lt_two_pi : fan.totalAngle < 2 * π := fan.angle_bound

end FiveFaceFan
end SixVertexUnfolding.ConvexPolyhedron
