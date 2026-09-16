import SixVertexUnfolding.Geometry.TriangleTopology

/-! Once an interior point is placed in a pocket component, the whole regular convex face follows. -/

namespace SixVertexUnfolding

/-- Boundary avoidance makes one interior seed sufficient for containment of the whole closed face. -/
theorem convex_face_in_closure_component (face boundary : Set Plane)
    (convex : Convex ℝ face) (regular : closure (interior face) = face)
    (safe : Disjoint (interior face) boundary) (seed : Plane) (inside : seed ∈ interior face) :
    face ⊆ closure (connectedComponentIn boundaryᶜ seed) := by
  have avoids : interior face ⊆ boundaryᶜ := by
    intro x member
    exact fun on_boundary => Set.disjoint_left.mp safe member on_boundary
  have contained := convex.interior.isPreconnected.subset_connectedComponentIn inside avoids
  rw [← regular]
  exact closure_mono contained

end SixVertexUnfolding
