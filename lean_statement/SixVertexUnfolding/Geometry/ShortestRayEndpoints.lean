import SixVertexUnfolding.Geometry.GeodesicFibers

/-! A shortest ray through a prescribed point has a farthest possible
endpoint. Everything here uses the actual intrinsic distance. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Endpoints reachable by a shortest route that goes through `b`. -/
def shortestExtensions (P : ConvexPolyhedron) (a b : frontier P.body) : Set (frontier P.body) :=
  {c | P.surfaceDist a c = P.surfaceDist a b + P.surfaceDist b c}

theorem shortestExtensions_self (P : ConvexPolyhedron) (a b : frontier P.body) :
    b ∈ P.shortestExtensions a b := by
  simp [shortestExtensions, P.surfaceDist_self b.property]

/-- Equality in the triangle inequality is a closed condition on the endpoint. -/
theorem shortestExtensions_compact (P : ConvexPolyhedron) (a b : frontier P.body) :
    IsCompact (P.shortestExtensions a b) := by
  letI : CompactSpace (frontier P.body) := isCompact_iff_compactSpace.mp
    (P.body_compact.of_isClosed_subset isClosed_frontier P.body_closed.frontier_subset)
  exact (isClosed_eq
    (P.surfaceDist_continuous.comp (continuous_const.prodMk continuous_id))
    (continuous_const.add (P.surfaceDist_continuous.comp
      (continuous_const.prodMk continuous_id)))).isCompact

/-- Extending a shortest ray again preserves its earlier intermediate point. -/
theorem shortestExtensions_trans (P : ConvexPolyhedron) (a b c d : frontier P.body)
    (through_b : c ∈ P.shortestExtensions a b) (through_c : d ∈ P.shortestExtensions a c) :
    d ∈ P.shortestExtensions a b := by
  change P.surfaceDist a d = P.surfaceDist a b + P.surfaceDist b d
  have first := P.surfaceDist_triangle a.property b.property d.property
  have second := P.surfaceDist_triangle b.property c.property d.property
  change P.surfaceDist a c = P.surfaceDist a b + P.surfaceDist b c at through_b
  change P.surfaceDist a d = P.surfaceDist a c + P.surfaceDist c d at through_c
  linarith

/-- Among all shortest extensions through `b`, an endpoint farthest from `a` exists. -/
theorem exists_farthest_shortest_extension (P : ConvexPolyhedron) (a b : frontier P.body) :
    ∃ c ∈ P.shortestExtensions a b, ∀ d ∈ P.shortestExtensions a b,
      P.surfaceDist a d ≤ P.surfaceDist a c := by
  exact (P.shortestExtensions_compact a b).exists_isMaxOn
    ⟨b, P.shortestExtensions_self a b⟩
    (P.surfaceDist_continuous.comp (continuous_const.prodMk continuous_id)).continuousOn

end SixVertexUnfolding.ConvexPolyhedron
