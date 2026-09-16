import SixVertexUnfolding.Geometry.FaceRouteSourceStability
import Mathlib.Topology.LocallyConstant.Basic

/-! One connected continuous route family ending inside a fixed face
has one fixed planar source copy for its entire terminal development. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Filter Topology

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Connectedness turns the local stability of an actual source copy into global constancy. -/
theorem face_route_family_source (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (x₀ : X) (target : X → frontier P.body)
    (routes : C(X, P.BoundaryCurve)) (member : ∀ x, routes x ∈ P.geodesicFiber a (target x))
    (different : ∀ x, a ≠ target x) (F : P.Face)
    (unique_face : ∀ x, ∀ G : P.Face, (target x : Space) ∈ G.val → G = F) :
    ∃ source ∈ P.sourceImages a F, ∀ x, P.HasTerminalSource (routes x) F source ∧
      P.surfaceDist a (target x) = dist source (P.faceCoordinates F (target x)) := by
  have first (x : X) : routes x 0 = a := congrArg Prod.fst (member x).2
  have last (x : X) : routes x 1 = target x := congrArg Prod.snd (member x).2
  have sources (x : X) : ∃ source ∈ P.sourceImages a F, P.HasTerminalSource (routes x) F source := by
    simpa only [first x] using graph.exists_terminal_source small_faces (routes x) (member x).1
      (by simpa only [first x, last x] using different x) F (by simpa only [last x] using unique_face x)
  choose source source_mem terminal using sources
  have locally_constant : IsLocallyConstant source := by
    apply (IsLocallyConstant.iff_eventually_eq source).mpr
    intro x
    obtain ⟨p, _, at_x, W, openW, xW, near⟩ := graph.geodesic_branch_terminal_source small_faces
      (routes x) (member x).1 (by simpa only [first x, last x] using different x) F
      (by simpa only [last x] using unique_face x)
    have same_x := (terminal x).unique at_x
    filter_upwards [routes.continuous.continuousAt.eventually (openW.mem_nhds xW)] with y yW
    exact ((terminal y).unique (near (routes y) yW (member y).1 ((first y).trans (first x).symm))).trans same_x.symm
  refine ⟨source x₀, source_mem x₀, ?_⟩
  intro x
  have constant : source x = source x₀ := locally_constant.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  have actual : P.HasTerminalSource (routes x) F (source x₀) := constant ▸ terminal x
  exact ⟨actual, by simpa only [first x, last x] using actual.distance (member x).1⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
