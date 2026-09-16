import SixVertexUnfolding.Geometry.ContinuousUniqueRoutes

/-! Uniqueness among normalized routes also determines the image of every
finite shortest path, even when that path pauses or uses a different speed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b : Space}

theorem shortest_normalization (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) :
    ∃ normal : P.SurfacePath a b, normal.IsShortest ∧ normal.length ≠ ⊤ ∧
      LipschitzWith normal.length.toNNReal normal.curve ∧ range normal.curve = range path.curve := by
  obtain ⟨normal, speed, image, shorter⟩ := path.exists_lipschitz_reparameterization finite
  have same : normal.length = path.length := le_antisymm shorter (shortest normal)
  exact ⟨normal, fun other => same ▸ shortest other, same ▸ finite, same ▸ speed, image⟩

end SurfacePath

/-- A unique normalized shortest route contains exactly the points of every finite shortest competitor. -/
theorem unique_shortest_image (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (unique : (P.geodesicFiber (f 0) (f 1)).Subsingleton)
    (path : P.SurfacePath (f 0) (f 1)) (shortest : path.IsShortest) (finite : path.length ≠ ⊤) :
    range path.curve = range (fun t => (f t : Space)) := by
  obtain ⟨normal, normal_shortest, normal_finite, normal_speed, same_image⟩ := path.shortest_normalization shortest finite
  have ends : P.curveEndpoints normal.boundaryCurve = (f 0, f 1) := by
    apply Prod.ext <;> apply Subtype.ext
    · exact normal.curve.source
    · exact normal.curve.target
  have same := unique ⟨normal.boundaryCurve_geodesic normal_shortest normal_finite normal_speed, ends⟩
    ⟨geodesic, rfl⟩
  rw [← same_image]
  have curves : (normal.curve : unitInterval → Space) = fun t => (f t : Space) :=
    funext (fun t => congrArg (fun g : P.BoundaryCurve => (g t : Space)) same)
  rw [curves]

end SixVertexUnfolding.ConvexPolyhedron
