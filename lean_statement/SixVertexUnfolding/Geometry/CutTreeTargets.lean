import SixVertexUnfolding.Geometry.CutEdgeRouteBranches

/-! Tree vertices and closed tree edges as points and paths on the actual boundary. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutLocusTree

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

/-- A graph vertex regarded as its actual surface point. -/
def vertexTarget (u : T.vertices) : frontier P.body :=
  ⟨u, P.cutSetInSpace_subset_boundary a (T.toEmbeddedCutGraph.vertex_in_trace u)⟩

theorem vertexTarget_cut (u : T.vertices) : T.vertexTarget u ∈ P.cutSet a :=
  (P.mem_cutSetInSpace a _).mp (T.toEmbeddedCutGraph.vertex_in_trace u)

theorem vertexTarget_different (u : T.vertices) : a ≠ T.vertexTarget u := by
  intro same
  have cut := T.vertexTarget_cut u
  rw [← same] at cut
  exact P.source_not_cutSet a cut

/-- The affine parametrization of a closed cut-tree edge, including its endpoints. -/
noncomputable def closedEdgeTarget {u v : T.vertices} (edge : T.graph.Adj u v) :
    C(unitInterval, frontier P.body) :=
  ⟨fun t => ⟨T.toEmbeddedCutGraph.edgePath edge t,
    P.cutSetInSpace_subset_boundary a (T.toEmbeddedCutGraph.edgePath edge t).property⟩,
    (continuous_subtype_val.comp (T.toEmbeddedCutGraph.edgePath edge).continuous).subtype_mk _⟩

theorem closedEdgeTarget_zero {u v : T.vertices} (edge : T.graph.Adj u v) :
    T.closedEdgeTarget edge 0 = T.vertexTarget u := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_zero _ _

theorem closedEdgeTarget_one {u v : T.vertices} (edge : T.graph.Adj u v) :
    T.closedEdgeTarget edge 1 = T.vertexTarget v := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one _ _

theorem closedEdgeTarget_interior {u v : T.vertices} (edge : T.graph.Adj u v) (t : Ioo (0 : ℝ) 1) :
    T.closedEdgeTarget edge ⟨t, t.property.1.le, t.property.2.le⟩ = T.openEdgeTarget edge t := rfl

theorem closedEdgeTarget_cut {u v : T.vertices} (edge : T.graph.Adj u v) (t : unitInterval) :
    T.closedEdgeTarget edge t ∈ P.cutSet a :=
  (P.mem_cutSetInSpace a _).mp (T.toEmbeddedCutGraph.edgePath edge t).property

end SixVertexUnfolding.ConvexPolyhedron.CutLocusTree
