import SixVertexUnfolding.Geometry.TwoRouteNeighborhoods
import SixVertexUnfolding.Geometry.SeparatedRouteContinuity

/-! Local continuous labels for the two actual shortest routes along the
regular cut locus. The labels enumerate the complete fiber at every target. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Targets in a chosen neighborhood whose actual shortest-route fiber has size two. -/
def twoRouteTargets (P : ConvexPolyhedron) (a : frontier P.body) (V : Set (frontier P.body)) :
    Set (frontier P.body) := {b | b ∈ V ∧ Nat.card (P.geodesicFiber a b) = 2}

/-- Two continuous, distinct route branches enumerating all routes on this part of the cut locus. -/
structure TwoRouteChart (P : ConvexPolyhedron) (a : frontier P.body) where
  domain : Set (frontier P.body)
  open_domain : IsOpen domain
  first : P.twoRouteTargets a domain → P.BoundaryCurve
  second : P.twoRouteTargets a domain → P.BoundaryCurve
  continuous_first : Continuous first
  continuous_second : Continuous second
  different : ∀ b, first b ≠ second b
  fiber_eq : ∀ b, P.geodesicFiber a b.val = {first b, second b}

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Around any nonvertex two-route target, both routes admit continuous local labels. -/
theorem exists_two_route_chart (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) (two : Nat.card (P.geodesicFiber a b) = 2) :
    ∃ chart : P.TwoRouteChart a, b ∈ chart.domain := by
  classical
  obtain ⟨V, openV, bV, U, W, openU, openW, apart, split⟩ :=
    graph.two_route_neighborhoods small_faces a b different not_vertex two
  have branches (c : P.twoRouteTargets a V) :
      ∃ f ∈ P.geodesicFiber a c.val ∩ U, ∃ g ∈ P.geodesicFiber a c.val ∩ W,
        f ≠ g ∧ P.geodesicFiber a c.val = {f, g} := split c.val c.property.1 c.property.2
  choose first first_mem second second_mem distinct pair using branches
  refine ⟨{
    domain := V
    open_domain := openV
    first := first
    second := second
    continuous_first := P.separated_route_selection_continuous a Subtype.val continuous_subtype_val
      first second pair U W openW apart (fun c => (first_mem c).2) (fun c => (second_mem c).2)
    continuous_second := ?_
    different := distinct
    fiber_eq := pair }, bV⟩
  exact P.separated_route_selection_continuous a Subtype.val continuous_subtype_val
    second first (fun c => (pair c).trans (pair_comm _ _)) W U openU apart.symm
    (fun c => (second_mem c).2) (fun c => (first_mem c).2)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
