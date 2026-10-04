import SixVertexUnfolding.Geometry.PrismDiagonalCapViews

/-! Whole-face cone containment at the two copies of the cap's cut vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
variable (net : graph.PrismFallbackDevelopment small_faces)
include prism_kind

/-- In either view, the left quadrilateral stays in its copied-source corner cone. -/
theorem PrismFallbackDevelopment.cap_left_corner_cone (q : Fin 2) :
    net.place (capLeftFace q) '' (graph.prismDiagonalFace small_faces (capLeftFace q)).val ⊆
      translatedCone ((net.capLeftFan prism_kind q).ray 3)
        ((net.capLeftFan prism_kind q).center - (net.capLeftFan prism_kind q).ray 3)
        (net.place (capLeftFace q) (graph.prismVertex (capOtherSource q)) - (net.capLeftFan prism_kind q).ray 3) := by
  have positions := net.cap_left_positions prism_kind q
  rw [positions.1, positions.2.1]
  have neighbors_eq : neighbors (capLeftFace q) (capSource q) = (capLeftVertex q, capOtherSource q) := by
    fin_cases q <;> decide
  have contained := net.face_subset_corner_cone prism_kind (capLeftFace q) (capSource q) (by fin_cases q <;> decide)
  simpa only [neighbors_eq] using contained

/-- The right cone uses the reverse order of the two original edges. -/
theorem PrismFallbackDevelopment.cap_right_corner_cone (q : Fin 2) :
    net.place (capRightFace q) '' (graph.prismDiagonalFace small_faces (capRightFace q)).val ⊆
      translatedCone ((net.capRightFan prism_kind q).ray 4)
        ((net.capRightFan prism_kind q).center - (net.capRightFan prism_kind q).ray 4)
        (net.place (capRightFace q) (graph.prismVertex (capOtherSource q)) - (net.capRightFan prism_kind q).ray 4) := by
  have positions := net.cap_right_positions prism_kind q
  rw [positions.1, positions.2.1]
  have neighbors_eq : neighbors (capRightFace q) (capSource q) = (capOtherSource q, capRightVertex q) := by
    fin_cases q <;> decide
  have contained := net.face_subset_corner_cone prism_kind (capRightFace q) (capSource q) (by fin_cases q <;> decide)
  simp only [neighbors_eq] at contained
  unfold translatedCone at contained ⊢
  rwa [twoRayCone_swap] at contained

/-- The fan's preceding ray is an actual vertex of each whole quadrilateral. -/
theorem PrismFallbackDevelopment.cap_corner_witnesses (q : Fin 2) :
    (net.capLeftFan prism_kind q).ray 2 ∈
      net.place (capLeftFace q) '' (graph.prismDiagonalFace small_faces (capLeftFace q)).val ∧
    (net.capRightFan prism_kind q).ray 3 ∈
      net.place (capRightFace q) '' (graph.prismDiagonalFace small_faces (capRightFace q)).val := by
  rw [(net.cap_left_positions prism_kind q).2.2.1, (net.cap_right_positions prism_kind q).2.2.1]
  exact ⟨⟨graph.prismVertex (capLeftWitness q),
      (graph.prismVertex_mem_face small_faces prism_kind _ _).mpr (by fin_cases q <;> decide), rfl⟩,
    ⟨graph.prismVertex (capRightWitness q),
      (graph.prismVertex_mem_face small_faces prism_kind _ _).mpr (by fin_cases q <;> decide), rfl⟩⟩

/-- The measured copied-source angles are the full quadrilateral angles. -/
theorem PrismFallbackDevelopment.cap_corner_angles (q : Fin 2) :
    angle (net.capLeftFan prism_kind q).center ((net.capLeftFan prism_kind q).ray 3)
      (net.place (capLeftFace q) (graph.prismVertex (capOtherSource q))) =
        graph.prismAngle small_faces (capLeftFace q) (capSource q) ∧
    angle (net.capRightFan prism_kind q).center ((net.capRightFan prism_kind q).ray 4)
      (net.place (capRightFace q) (graph.prismVertex (capOtherSource q))) =
        graph.prismAngle small_faces (capRightFace q) (capSource q) := by
  have left_neighbors : neighbors (capLeftFace q) (capSource q) = (capLeftVertex q, capOtherSource q) := by
    fin_cases q <;> decide
  have right_neighbors : neighbors (capRightFace q) (capSource q) = (capOtherSource q, capRightVertex q) := by
    fin_cases q <;> decide
  constructor
  · rw [(net.cap_left_positions prism_kind q).1, (net.cap_left_positions prism_kind q).2.1]
    simpa only [left_neighbors] using
      net.placed_corner_angle prism_kind (capLeftFace q) (capSource q) (by fin_cases q <;> decide)
  · rw [(net.cap_right_positions prism_kind q).1, (net.cap_right_positions prism_kind q).2.1, angle_comm]
    simpa only [right_neighbors] using
      net.placed_corner_angle prism_kind (capRightFace q) (capSource q) (by fin_cases q <;> decide)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
