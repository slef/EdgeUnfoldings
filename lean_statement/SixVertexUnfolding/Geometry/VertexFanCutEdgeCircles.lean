import SixVertexUnfolding.Geometry.CutEdgeTriangles
import SixVertexUnfolding.Geometry.VertexFanCornerCircleLength

/-! The two actual triangles along a cut-tree edge provide angular
circle arcs at an original vertex endpoint. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set EuclideanGeometry

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Both circular triangle sections have nonexpanding angular parametrizations. -/
theorem cut_edge_corner_circle_arcs {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : CutEdgeTriangles T edge)
    (at_vertex : (u : Space) = (pole : Space)) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
      ∃ f g : ℝ → AddCircle (fan.totalAngle),
        (∀ s ∈ Icc (0 : ℝ) (angle D.model.first D.model.left D.model.right),
          ∀ t ∈ Icc (0 : ℝ) (angle D.model.first D.model.left D.model.right), dist (f s) (f t) ≤ dist s t) ∧
        (∀ s ∈ Icc (0 : ℝ) (angle D.model.second D.model.left D.model.right),
          ∀ t ∈ Icc (0 : ℝ) (angle D.model.second D.model.left D.model.right), dist (g s) (g t) ≤ dist s t) ∧
        (∀ z : convexHull ℝ ({D.model.first, D.model.left, D.model.right} : Set Plane),
          dist (z : Plane) D.model.left = ρ →
          fan.fanCircleMap ((D.first_triangle.homeomorph.symm z).val : Space) ∈
            f '' Icc (0 : ℝ) (angle D.model.first D.model.left D.model.right)) ∧
        (∀ z : convexHull ℝ ({D.model.second, D.model.left, D.model.right} : Set Plane),
          dist (z : Plane) D.model.left = ρ →
          fan.fanCircleMap ((D.second_triangle.homeomorph.symm z).val : Space) ∈
            g '' Icc (0 : ℝ) (angle D.model.second D.model.left D.model.right)) := by
  let first_corner : convexHull ℝ ({D.model.first, D.model.left, D.model.right} : Set Plane) :=
    ⟨D.model.left, subset_convexHull ℝ _ (by simp)⟩
  let second_corner : convexHull ℝ ({D.model.second, D.model.left, D.model.right} : Set Plane) :=
    ⟨D.model.left, subset_convexHull ℝ _ (by simp)⟩
  have first_target : D.first 0 1 = T.vertexTarget u :=
    (congrArg Prod.snd (D.member 0).1.2).trans (T.closedEdgeTarget_zero edge)
  have second_target : D.second 0 1 = T.vertexTarget u :=
    (congrArg Prod.snd (D.member 0).2.2).trans (T.closedEdgeTarget_zero edge)
  have first_at_pole : ((D.first_triangle.homeomorph.symm first_corner).val : Space) = pole := by
    rw [D.first_triangle.fold_left_corner first_corner rfl, first_target]
    exact at_vertex
  have second_at_pole : ((D.second_triangle.homeomorph.symm second_corner).val : Space) = pole := by
    rw [D.second_triangle.fold_left_corner second_corner rfl, second_target]
    exact at_vertex
  obtain ⟨ε, ep, first_arc⟩ := fan.folded_corner_circle_arc small_faces D.first_triangle D.model.noncollinear.1
    first_corner rfl first_at_pole
  obtain ⟨δ, dp, second_arc⟩ := fan.folded_corner_circle_arc small_faces D.second_triangle D.model.noncollinear.2
    second_corner rfl second_at_pole
  refine ⟨min ε δ, lt_min ep dp, ?_⟩
  intro ρ hr
  obtain ⟨f, boundedf, coversf⟩ := first_arc ρ ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
  obtain ⟨g, boundedg, coversg⟩ := second_arc ρ ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩
  exact ⟨f, g, boundedf, boundedg, coversf, coversg⟩

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
