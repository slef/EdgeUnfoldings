import SixVertexUnfolding.Geometry.RegularCutTree
import SixVertexUnfolding.Geometry.GlobalTwoRouteBranches
import Mathlib.Analysis.Convex.Contractible

/-! Each open cut-tree edge carries two continuous families of actual
shortest routes, with a fixed choice of labels along the entire edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutLocusTree

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

/-- The ordinary affine parametrization of an open tree edge, on the actual boundary. -/
noncomputable def openEdgeTarget {u v : T.vertices} (edge : T.graph.Adj u v) :
    C(Ioo (0 : ℝ) 1, frontier P.body) := by
  let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap (u : Space) (v : Space)
  have inside (t : Ioo (0 : ℝ) 1) : line t ∈ openSegment ℝ (u : Space) (v : Space) := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, t.property, rfl⟩
  exact ⟨fun t => ⟨line t, P.cutSetInSpace_subset_boundary a
      ((T.trace (line t)).mpr (Or.inr ⟨u, v, edge, inside t⟩))⟩,
    (line.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _⟩

theorem openEdgeTarget_inside {u v : T.vertices} (edge : T.graph.Adj u v) (t : Ioo (0 : ℝ) 1) :
    (T.openEdgeTarget edge t : Space) ∈ openSegment ℝ (u : Space) (v : Space) := by
  rw [openSegment_eq_image_lineMap]
  exact ⟨t, t.property, rfl⟩

theorem openEdgeTarget_injective {u v : T.vertices} (edge : T.graph.Adj u v) :
    Function.Injective (T.openEdgeTarget edge) := by
  intro s t same
  apply Subtype.ext
  exact AffineMap.lineMap_injective ℝ (fun equal => edge.ne (Subtype.ext equal))
    (congrArg (fun b : frontier P.body => (b : Space)) same)

/-- The parameter interval covers the entire open edge. -/
theorem mem_range_openEdgeTarget {u v : T.vertices} (edge : T.graph.Adj u v)
    (b : frontier P.body) :
    b ∈ range (T.openEdgeTarget edge) ↔
      (b : Space) ∈ openSegment ℝ (u : Space) (v : Space) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact T.openEdgeTarget_inside edge t
  · intro inside
    rw [openSegment_eq_image_lineMap] at inside
    obtain ⟨t, ht, at_t⟩ := inside
    exact ⟨⟨t, ht⟩, Subtype.ext at_t⟩

theorem openEdgeTarget_different {u v : T.vertices} (edge : T.graph.Adj u v) (t : Ioo (0 : ℝ) 1) :
    a ≠ T.openEdgeTarget edge t := by
  intro same
  have cut := T.open_edge_cut edge (T.openEdgeTarget edge t) (T.openEdgeTarget_inside edge t)
  rw [← same] at cut
  exact P.source_not_cutSet a cut

theorem openEdgeTarget_nonvertex {u v : T.vertices} (edge : T.graph.Adj u v) (t : Ioo (0 : ℝ) 1) :
    (T.openEdgeTarget edge t : Space) ∉ P.vertices := by
  intro vertex
  exact T.open_edge_regular edge (T.openEdgeTarget edge t) (T.openEdgeTarget_inside edge t)
    (Or.inr ⟨vertex, (T.openEdgeTarget_different edge t).symm⟩)

end CutLocusTree

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every open edge has two globally continuous, distinct route branches, enumerating its whole route fiber. -/
theorem cut_edge_continuous_routes (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) :
    ∃ first second : C(Ioo (0 : ℝ) 1, P.BoundaryCurve), (∀ t, first t ≠ second t) ∧
      ∀ t, P.geodesicFiber a (T.openEdgeTarget edge t) = {first t, second t} := by
  letI : ContractibleSpace (Ioo (0 : ℝ) 1) :=
    Convex.contractibleSpace (convex_Ioo (0 : ℝ) 1) ⟨1 / 2, by norm_num⟩
  letI : LocPathConnectedSpace (Ioo (0 : ℝ) 1) := isOpen_Ioo.locPathConnectedSpace
  exact graph.continuous_two_route_branches small_faces a (⟨1 / 2, by norm_num⟩ : Ioo (0 : ℝ) 1)
    (T.openEdgeTarget edge) (T.openEdgeTarget edge).continuous
    (T.openEdgeTarget_different edge) (T.openEdgeTarget_nonvertex edge)
    (fun t => graph.cut_tree_open_edge_two_routes small_faces a T edge (T.openEdgeTarget edge t)
      (T.openEdgeTarget_inside edge t))

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
