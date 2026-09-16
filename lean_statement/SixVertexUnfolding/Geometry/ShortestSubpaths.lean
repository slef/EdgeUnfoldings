import SixVertexUnfolding.Geometry.ShortestSurfacePaths
import SixVertexUnfolding.Geometry.StraightShortestPaths

/-! Portions of shortest paths are shortest. In particular, a shortest path
cannot leave a convex face between two visits to that face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set
open scoped ENNReal NNReal

variable {P : ConvexPolyhedron} {a b : Space}

/-- Follow a portion of a surface path, pausing before its start and after its end. -/
noncomputable def portion (path : P.SurfacePath a b) (s t : unitInterval) (ordered : s ≤ t) :
    P.SurfacePath (path.curve s) (path.curve t) where
  curve := {
    toFun := fun u => path.curve (min t (max s u))
    continuous_toFun := path.curve.continuous.comp (by fun_prop)
    source' := by simp only [max_eq_left (unitInterval.nonneg' (t := s)), min_eq_right ordered]
    target' := by simp only [max_eq_right (unitInterval.le_one' (t := s)),
      min_eq_left (unitInterval.le_one' (t := t))] }
  on_surface u := path.on_surface _

/-- A portion's length is the variation on precisely its parameter interval. -/
theorem portion_length (path : P.SurfacePath a b) (s t : unitInterval) (ordered : s ≤ t) :
    (path.portion s t ordered).length = eVariationOn path.curve (Icc s t) := by
  rw [length_eq_variation]
  change eVariationOn (path.curve ∘ (fun u => min t (max s u))) Set.univ = _
  rw [eVariationOn.comp_eq_of_monotoneOn _ _
    (by intro u hu v hv h; exact min_le_min_left _ (max_le_max_left _ h))]
  congr 1
  ext u
  constructor
  · rintro ⟨v, _, rfl⟩
    exact ⟨le_min ordered (le_max_left _ _), min_le_left _ _⟩
  · intro hu
    exact ⟨u, mem_univ _, by dsimp; rw [max_eq_right hu.1, min_eq_right hu.2]⟩

/-- Every portion of a finite-length path has finite length. -/
theorem portion_finite (path : P.SurfacePath a b) (finite : path.length ≠ ⊤)
    (s t : unitInterval) (ordered : s ≤ t) : (path.portion s t ordered).length ≠ ⊤ := by
  rw [portion_length]
  apply ne_top_of_le_ne_top (path.length_eq_variation ▸ finite)
  exact eVariationOn.mono _ (subset_univ _)

/-- Splitting at two parameters partitions the whole length into three lengths. -/
theorem length_split_three (path : P.SurfacePath a b) (s t : unitInterval) (ordered : s ≤ t) :
    path.length = (path.portion 0 s unitInterval.nonneg').length +
      (path.portion s t ordered).length + (path.portion t 1 unitInterval.le_one').length := by
  simp only [portion_length]
  have first := eVariationOn.Icc_add_Icc path.curve (s := Set.univ)
    (unitInterval.nonneg' (t := s)) ordered (mem_univ s)
  have second := eVariationOn.Icc_add_Icc path.curve (s := Set.univ)
    (unitInterval.nonneg' (t := t)) (unitInterval.le_one' (t := t)) (mem_univ t)
  simp only [univ_inter] at first second
  rw [first, second, path.length_eq_variation]
  congr 1
  ext u
  exact ⟨fun _ => u.property, fun _ => mem_univ _⟩

/-- A shorter replacement for any portion would shorten the whole surface route. -/
theorem portion_shortest (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (s t : unitInterval) (ordered : s ≤ t) :
    (path.portion s t ordered).IsShortest := by
  intro other
  let first := path.portion 0 s unitInterval.nonneg'
  let last := path.portion t 1 unitInterval.le_one'
  let replacement := (first.join other).join last
  have comparison : path.length ≤ replacement.length := by
    have ends : path.curve 0 = a ∧ path.curve 1 = b := ⟨path.curve.source, path.curve.target⟩
    let competitor : P.SurfacePath a b := {
      curve := replacement.curve.cast ends.1.symm ends.2.symm
      on_surface := replacement.on_surface }
    exact shortest competitor
  rw [path.length_split_three s t ordered] at comparison
  change _ ≤ ((first.join other).join last).length at comparison
  rw [join_length, join_length] at comparison
  exact ENNReal.le_of_add_le_add_left (path.portion_finite finite 0 s unitInterval.nonneg')
    (ENNReal.le_of_add_le_add_right (path.portion_finite finite t 1 unitInterval.le_one') comparison)

/-- Between two points of one face, a shortest surface path follows their straight segment. -/
theorem shortest_portion_range (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (F : P.Face) (s t : unitInterval) (ordered : s ≤ t)
    (hs : path.curve s ∈ F.val) (ht : path.curve t ∈ F.val) :
    ∀ u ∈ Icc s t, path.curve u ∈ segment ℝ (path.curve s) (path.curve t) := by
  intro u hu
  apply (path.portion s t ordered).shortest_cofacial_range_subset
    (path.portion_shortest shortest finite s t ordered) F hs ht
  refine ⟨u, ?_⟩
  change path.curve (min t (max s u)) = path.curve u
  rw [max_eq_right hu.1, min_eq_right hu.2]

/-- A shortest path visits each whole face in one uninterrupted parameter interval. -/
theorem shortest_face_visits_ordConnected (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤) (F : P.Face) :
    OrdConnected {t : unitInterval | path.curve t ∈ F.val} := by
  constructor
  intro s hs t ht u hu
  exact F.convex.segment_subset hs ht
    (path.shortest_portion_range shortest finite F s t (hu.1.trans hu.2) hs ht u hu)

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
