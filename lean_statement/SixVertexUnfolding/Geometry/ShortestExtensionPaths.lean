import SixVertexUnfolding.Geometry.ShortestRayEndpoints
import SixVertexUnfolding.Geometry.UniqueShortestImages

/-! The distance equality defining a shortest extension is realized by an
actual normalized shortest route through the specified intermediate point. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Equality in the intrinsic triangle inequality yields a shortest route through the middle point. -/
theorem shortest_extension_path (P : ConvexPolyhedron) (a b c : frontier P.body)
    (extension : c ∈ P.shortestExtensions a b) :
    ∃ f ∈ P.geodesicFiber a c, ∃ t : unitInterval, f t = b := by
  obtain ⟨front, front_shortest, front_finite, front_length⟩ :=
    P.exists_surface_distance_path a.property b.property
  obtain ⟨tail, tail_shortest, tail_finite, tail_length⟩ :=
    P.exists_surface_distance_path b.property c.property
  let joined := front.join tail
  have finite : joined.length ≠ ⊤ := front.join_finite tail front_finite tail_finite
  have exact_length : joined.length = P.surfaceEDist a c := by
    apply (ENNReal.toReal_eq_toReal_iff' finite (P.surfaceEDist_ne_top a.property c.property)).mp
    rw [show joined.length = front.length + tail.length from front.join_length tail,
      ENNReal.toReal_add front_finite tail_finite, front_length, tail_length]
    exact extension.symm
  have shortest : joined.IsShortest := fun other => exact_length ▸ other.surfaceEDist_le_length
  obtain ⟨normal, optimal, bounded, speed, image⟩ := joined.shortest_normalization shortest finite
  have middle : (b : Space) ∈ range normal.curve := by
    rw [image]
    change (b : Space) ∈ range (front.curve.trans tail.curve)
    rw [Path.trans_range]
    exact Or.inl ⟨1, front.curve.target⟩
  obtain ⟨t, at_t⟩ := middle
  refine ⟨normal.boundaryCurve, ⟨normal.boundaryCurve_geodesic optimal bounded speed, ?_⟩,
    t, Subtype.ext at_t⟩
  apply Prod.ext <;> apply Subtype.ext
  · exact normal.curve.source
  · exact normal.curve.target

end SixVertexUnfolding.ConvexPolyhedron
