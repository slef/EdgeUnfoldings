import SixVertexUnfolding.Geometry.TreeTransitionChoice
import SixVertexUnfolding.Geometry.PlacedCutEdgeTriangles

/-! One global choice of frames aligns both whole radial triangle maps
across every cut-tree edge. No pairwise re-selection of coordinates occurs. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Frames for a fixed collection of local cut-edge triangle placements. -/
structure CutTreeFrames {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a)
    (charts : ∀ {u v : T.vertices} (edge : T.graph.Adj u v), PlacedCutEdgeTriangles T edge) where
  transition : ∀ {u v : T.vertices}, T.graph.Adj u v → Plane ≃ᵃⁱ[ℝ] Plane
  frame : T.vertices → Plane ≃ᵃⁱ[ℝ] Plane
  reverses : ∀ {u v : T.vertices} (edge : T.graph.Adj u v),
    (charts edge).Reverses (charts edge.symm) (transition edge)
  compatible : ∀ {u v : T.vertices} (edge : T.graph.Adj u v) (x : Plane),
    frame v (transition edge x) = frame u x

namespace CutTreeFrames

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {charts : ∀ {u v : T.vertices} (edge : T.graph.Adj u v), PlacedCutEdgeTriangles T edge}

/-- The same globally placed triangle pair is obtained from either edge orientation. -/
theorem global_reversal (frames : CutTreeFrames T charts)
    {u v : T.vertices} (edge : T.graph.Adj u v) :
    ((charts edge).inFrame (frames.frame u)).Reverses
      ((charts edge.symm).inFrame (frames.frame v)) (AffineIsometryEquiv.refl ℝ Plane) :=
  (frames.reverses edge).in_common_frame (frames.frame u) (frames.frame v) (frames.compatible edge)

end CutTreeFrames

/-- Arbitrarily chosen genuine local triangle charts have coherent reverse-edge frames. -/
theorem exists_cut_tree_frames {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a)
    (charts : ∀ {u v : T.vertices} (edge : T.graph.Adj u v), PlacedCutEdgeTriangles T edge) :
    Nonempty (CutTreeFrames T charts) := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  let root : T.vertices := Classical.choice T.tree.connected.nonempty
  obtain ⟨motion, frame, valid, _, compatible⟩ := TreeFrames.exists_frames_for_transitions
    T.graph T.tree root (fun {_ _} edge transition => (charts edge).Reverses (charts edge.symm) transition)
    (fun {_ _} edge => (charts edge).exists_reversal (charts edge.symm))
    (fun {_ _} _ _ valid => valid.symm)
  exact ⟨⟨@motion, frame, valid, compatible⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
