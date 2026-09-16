import SixVertexUnfolding.Geometry.CutEndpointRetraction
import SixVertexUnfolding.Geometry.PuncturedBoundaryContraction

/-! The cut set itself is contractible: compose a contraction of the
punctured boundary with the continuous ray-endpoint retraction. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The actual vertex-augmented cut set is contractible. -/
theorem cutSet_contractible (a : frontier P.body) : ContractibleSpace (P.cutSet a) := by
  let X := {b : frontier P.body // b ≠ a}
  let Y := P.cutSet a
  letI : ContractibleSpace X := P.punctured_boundary_contractible a
  let inclusion : C(Y, X) := ⟨fun c =>
    ⟨c.val, ne_of_mem_of_not_mem c.property (P.source_not_cutSet a)⟩,
    continuous_subtype_val.subtype_mk _⟩
  let retract : C(X, Y) := ⟨graph.cutEndpoint small_faces a, graph.cutEndpoint_continuous small_faces a⟩
  have null := ((id_nullhomotopic X).comp_left inclusion).comp_right retract
  have identity : retract.comp ((ContinuousMap.id X).comp inclusion) = ContinuousMap.id Y := by
    apply ContinuousMap.ext
    intro c
    exact graph.cutEndpoint_fixes small_faces a c
  apply (contractible_iff_id_nullhomotopic Y).mpr
  rwa [identity] at null

include graph small_faces in
/-- The embedded graph's spatial trace has this same contractible topology. -/
theorem cutSetInSpace_contractible (a : frontier P.body) : ContractibleSpace (P.cutSetInSpace a) := by
  letI : ContractibleSpace (P.cutSet a) := graph.cutSet_contractible small_faces a
  let h : P.cutSet a ≃ₜ P.cutSetInSpace a :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage (P.cutSet a)
  exact h.symm.contractibleSpace

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
