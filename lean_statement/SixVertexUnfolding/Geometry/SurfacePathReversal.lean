import SixVertexUnfolding.Geometry.ShortestSurfacePaths

/-! Reversing a surface route preserves its exact arc length and shortestness. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set
open scoped ENNReal NNReal

variable {P : ConvexPolyhedron} {a b : Space}

/-- Traverse the same boundary route backwards. -/
noncomputable def reverse (path : P.SurfacePath a b) : P.SurfacePath b a where
  curve := path.curve.symm
  on_surface t := path.on_surface (unitInterval.symm t)

/-- Reversal preserves arc length, including infinite length. -/
theorem reverse_length (path : P.SurfacePath a b) : path.reverse.length = path.length := by
  rw [length_eq_variation, path.length_eq_variation]
  change eVariationOn (path.curve ∘ unitInterval.symm) Set.univ = _
  rw [eVariationOn.comp_eq_of_antitoneOn _ _ (unitInterval.strictAnti_symm.antitone.antitoneOn Set.univ),
    image_univ, unitInterval.symm_bijective.surjective.range_eq]

/-- Reversing a shortest route still gives a shortest route. -/
theorem reverse_shortest (path : P.SurfacePath a b) (shortest : path.IsShortest) :
    path.reverse.IsShortest := by
  intro other
  rw [reverse_length]
  simpa only [reverse_length] using shortest other.reverse

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
