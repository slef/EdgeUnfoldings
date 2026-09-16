import SixVertexUnfolding.Geometry.TwoRouteCharts
import SixVertexUnfolding.Geometry.SmallPolyhedronTwoRouteNeighborhoods

/-! Local continuous labels for the two actual shortest routes along the
regular cut locus. The labels enumerate the complete fiber at every target.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Around any nonvertex two-route target, both routes admit continuous local labels. -/
theorem small_exists_two_route_chart (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) (two : Nat.card (P.geodesicFiber a b) = 2) :
    ∃ chart : P.TwoRouteChart a, b ∈ chart.domain := by
  classical
  obtain ⟨V, openV, bV, U, W, openU, openW, apart, split⟩ :=
    small_two_route_neighborhoods size small_faces a b different not_vertex two
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

end SixVertexUnfolding.ConvexPolyhedron
