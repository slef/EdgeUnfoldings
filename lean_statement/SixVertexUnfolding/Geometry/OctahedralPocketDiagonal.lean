import SixVertexUnfolding.Geometry.OctahedralPocketCandidate
import SixVertexUnfolding.Geometry.QuadrilateralDiagonal

/-! Both actual pocket candidates admit a diagonal with the two remaining corners strictly on opposite sides. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The last-triple overlap gives an actual triangulable quadrilateral, with no extra position assumptions. -/
theorem exists_last_pocket_diagonal
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (overlap : ¬ net.Separated (true, 1) (true, 3)) :
    ∃ p, p ∈ interior (net.placedTriangle (true, 1)) ∧ p ∈ interior (net.placedTriangle (true, 3)) ∧
      QuadrilateralBoundary (net.patch 1).left p (net.patch 3).right 0 ∧
      (det ((net.patch 3).right - (net.patch 1).left) (p - (net.patch 1).left) *
          det ((net.patch 3).right - (net.patch 1).left) (0 - (net.patch 1).left) < 0 ∨
        det (0 - p) ((net.patch 1).left - p) * det (0 - p) ((net.patch 3).right - p) < 0) := by
  classical
  let a := (net.patch 1).left
  let b := (net.patch 3).right
  let lines : Finset (Plane × Plane) := {(a, b), (a, 0), (b, 0)}
  obtain ⟨p, left, right, boundary, avoids⟩ := net.exists_last_pocket_boundary source_order maximal overlap lines
  exact ⟨p, left, right, boundary, boundary.separating_diagonal
    (avoids (a, b) (by simp [lines])) (avoids (a, 0) (by simp [lines])) (avoids (b, 0) (by simp [lines]))⟩

/-- The same diagonal certificate holds for the reflected first-triple overlap. -/
theorem exists_first_pocket_diagonal
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (overlap : ¬ net.Separated (true, 0) (true, 2)) :
    ∃ p, p ∈ interior (net.placedTriangle (true, 0)) ∧ p ∈ interior (net.placedTriangle (true, 2)) ∧
      QuadrilateralBoundary (net.patch 0).left p (net.patch 2).right 0 ∧
      (det ((net.patch 2).right - (net.patch 0).left) (p - (net.patch 0).left) *
          det ((net.patch 2).right - (net.patch 0).left) (0 - (net.patch 0).left) < 0 ∨
        det (0 - p) ((net.patch 0).left - p) * det (0 - p) ((net.patch 2).right - p) < 0) := by
  classical
  let a := (net.patch 0).left
  let b := (net.patch 2).right
  let lines : Finset (Plane × Plane) := {(a, b), (a, 0), (b, 0)}
  obtain ⟨p, left, right, boundary, avoids⟩ := net.exists_first_pocket_boundary source_order maximal overlap lines
  exact ⟨p, left, right, boundary, boundary.separating_diagonal
    (avoids (a, b) (by simp [lines])) (avoids (a, 0) (by simp [lines])) (avoids (b, 0) (by simp [lines]))⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
