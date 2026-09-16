import SixVertexUnfolding.Geometry.CutEdgeRouteBranches
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTree
import SixVertexUnfolding.Geometry.SmallPolyhedronGlobalTwoRouteBranches

/-! Each open cut-tree edge carries two continuous families of actual
shortest routes, with a fixed choice of labels along the entire edge.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Every open edge has two globally continuous, distinct route branches, enumerating its whole route fiber. -/
theorem small_cut_edge_continuous_routes (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) :
    ∃ first second : C(Ioo (0 : ℝ) 1, P.BoundaryCurve), (∀ t, first t ≠ second t) ∧
      ∀ t, P.geodesicFiber a (T.openEdgeTarget edge t) = {first t, second t} := by
  letI : ContractibleSpace (Ioo (0 : ℝ) 1) :=
    Convex.contractibleSpace (convex_Ioo (0 : ℝ) 1) ⟨1 / 2, by norm_num⟩
  letI : LocPathConnectedSpace (Ioo (0 : ℝ) 1) := isOpen_Ioo.locPathConnectedSpace
  exact small_continuous_two_route_branches size small_faces a (⟨1 / 2, by norm_num⟩ : Ioo (0 : ℝ) 1)
    (T.openEdgeTarget edge) (T.openEdgeTarget edge).continuous
    (T.openEdgeTarget_different edge) (T.openEdgeTarget_nonvertex edge)
    (fun t => small_cut_tree_open_edge_two_routes size small_faces a T edge (T.openEdgeTarget edge t)
      (T.openEdgeTarget_inside edge t))

end SixVertexUnfolding.ConvexPolyhedron
