import SixVertexUnfolding.Geometry.OctahedralClosedLink
import SixVertexUnfolding.Curvature.Selection
import SixVertexUnfolding.Curvature.PairedPoles

/-! Curvature choices and strict link slack for the actual six-vertex solid. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Every actual subdivision corner is strictly smaller than half its vertex's angle sum. -/
theorem cornerAngle_link_bound (t : Fin 8) (i : Fin 3) :
    2 * graph.cornerAngle t i < graph.totalAngleAt (corner t i) := by
  apply graph.vertex_link_bound small_faces
  · exact (corner_injective t).ne ((by decide : ∀ i : Fin 3, i + 1 ≠ i) i)
  · exact (corner_injective t).ne ((by decide : ∀ i : Fin 3, i + 2 ≠ i) i)
  · exact corner_ne_opposite t (i + 1) i

include small_faces in
/-- The positive link slack used in the paired-pole identities comes from spatial angles. -/
theorem cornerAngle_linkSlack_pos (t : Fin 8) (i : Fin 3) :
    0 < PairedPoles.linkSlack (graph.curvature (corner t i)) (graph.cornerAngle t i) := by
  have strict := graph.cornerAngle_link_bound small_faces t i
  unfold PairedPoles.linkSlack curvature
  linarith

/-- Gauss--Bonnet expressed in the pole and equator labels of any chosen opening. -/
theorem curvature_poles_equator (v : Fin 6) :
    graph.curvature v + graph.curvature (opposite v) +
      (∑ i : Fin 4, graph.curvature (fanNeighbor v i)) = 4 * Real.pi := by
  rw [sum_poles_equator, graph.sum_curvature]

/-- Either endpoint of a fixed opposite pair can be chosen as the sharper source. -/
theorem exists_sharper_pole (v : Fin 6) :
    ∃ source, (source = v ∨ source = opposite v) ∧
      graph.curvature (opposite source) ≤ graph.curvature source := by
  by_cases ordered : graph.curvature (opposite v) ≤ graph.curvature v
  · exact ⟨v, Or.inl rfl, ordered⟩
  · exact ⟨opposite v, Or.inr rfl, by rw [opposite_opposite]; exact (le_of_not_ge ordered)⟩

include small_faces in
/-- A maximum-curvature equator vertex supplies all scalar slit conditions in the actual solid.
This chooses the slit endpoint; planar nonoverlap is a separate geometric obligation. -/
theorem exists_curvature_slit (source : Fin 6) :
    ∃ slit : Fin 4,
      (∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) ∧
      Real.pi < 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source) ∧
      (Real.pi ≤ graph.curvature source ∨ ∀ i,
        Real.pi < graph.curvature (opposite source) + graph.curvature (fanNeighbor source slit) +
          graph.curvature (fanNeighbor source i)) := by
  exact Curvature.exists_slit_satisfying_criterion (graph.curvature_poles_equator source)
    (graph.curvature_lt_two_pi source) (graph.curvature_pos small_faces (opposite source))
    (fun i => graph.curvature_pos small_faces (fanNeighbor source i))

include small_faces in
/-- Every opposite pair admits a sharper source and an equator slit satisfying the curvature gates. -/
theorem exists_selected_poles_and_slit (v : Fin 6) :
    ∃ source slit,
      (source = v ∨ source = opposite v) ∧
      graph.curvature (opposite source) ≤ graph.curvature source ∧
      (Real.pi ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ Real.pi) ∧
      (∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) ∧
      Real.pi < 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source) ∧
      (Real.pi ≤ graph.curvature source ∨ ∀ i,
        Real.pi < graph.curvature (opposite source) + graph.curvature (fanNeighbor source slit) +
          graph.curvature (fanNeighbor source i)) := by
  obtain ⟨source, endpoint, ordered⟩ := graph.exists_sharper_pole v
  obtain ⟨slit, maximal, threshold, low_bounds⟩ := graph.exists_curvature_slit small_faces source
  exact ⟨source, slit, endpoint, ordered, Curvature.half_fan_alternative ordered,
    maximal, threshold, low_bounds⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
