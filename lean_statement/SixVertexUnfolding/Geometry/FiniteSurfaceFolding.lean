import SixVertexUnfolding.Geometry.FiniteAffinePasting
import SixVertexUnfolding.Geometry.SurfaceDistance

/-! A finite collection of rigid planar pieces, joined consistently, folds
straight segments into surface paths with no increase in length. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set
open scoped ENNReal NNReal

/-- Internal data for folding a finite developed patch back onto the surface. -/
structure FiniteSurfaceFolding (P : ConvexPolyhedron) (ι : Type*) where
  piece : ι → Set Plane
  closed : ∀ i, IsClosed (piece i)
  convex : ∀ i, Convex ℝ (piece i)
  place : ι → Plane →ᵃ[ℝ] Space
  rigid : ∀ i x y, dist (place i x) (place i y) = dist x y
  on_surface : ∀ i x, x ∈ piece i → place i x ∈ frontier P.body
  joined : ∀ i j x, x ∈ piece i → x ∈ piece j → place i x = place j x

namespace FiniteSurfaceFolding

variable {P : ConvexPolyhedron} {ι : Type*} [Finite ι] (fold : P.FiniteSurfaceFolding ι)

/-- All developed pieces together. -/
def domain : Set Plane := ⋃ i, fold.piece i

/-- Use the formula from any piece containing the point. -/
noncomputable def map (x : Plane) : Space := by
  classical
  exact if h : ∃ i, x ∈ fold.piece i then fold.place h.choose x else 0

omit [Finite ι] in
theorem map_on_piece (i : ι) {x : Plane} (hx : x ∈ fold.piece i) :
    fold.map x = fold.place i x := by
  classical
  rw [map, dif_pos ⟨i, hx⟩]
  exact fold.joined _ i x (Exists.choose_spec (⟨i, hx⟩ : ∃ j, x ∈ fold.piece j)) hx

omit [Finite ι] in
theorem map_on_surface {x : Plane} (hx : x ∈ fold.domain) :
    fold.map x ∈ frontier P.body := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rw [fold.map_on_piece i hi]
  exact fold.on_surface i x hi

theorem continuousOn : ContinuousOn fold.map fold.domain := by
  apply (locallyFinite_of_finite fold.piece).continuousOn_iUnion fold.closed
  intro i
  exact (fold.place i).continuous_of_finiteDimensional.continuousOn.congr
    (fun _ hx => fold.map_on_piece i hx)

/-- Fold a segment that lies entirely in the developed patch. -/
noncomputable def segmentPath (x y : Plane) (inside : segment ℝ x y ⊆ fold.domain) :
    P.SurfacePath (fold.map x) (fold.map y) where
  curve := {
    toFun := fun t => fold.map (Path.segment x y t)
    continuous_toFun := fold.continuousOn.comp_continuous (Path.segment x y).continuous
      (fun t => inside (by rw [← Path.range_segment]; exact ⟨t, rfl⟩))
    source' := by simp
    target' := by simp }
  on_surface t := fold.map_on_surface (inside (by rw [← Path.range_segment]; exact ⟨t, rfl⟩))

/-- On each time interval, the folded straight segment has the original speed bound. -/
theorem segment_distance_le (x y : Plane) (inside : segment ℝ x y ⊆ fold.domain)
    (s t : unitInterval) (ordered : s ≤ t) :
    dist (fold.map (Path.segment x y s)) (fold.map (Path.segment x y t)) ≤
      dist x y * ((t : ℝ) - (s : ℝ)) := by
  let line : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap x y
  let pieces : ι → Set ℝ := fun i => line ⁻¹' fold.piece i
  let maps : ι → ℝ →ᵃ[ℝ] Space := fun i => (fold.place i).comp line
  have closed (i : ι) : IsClosed (pieces i) :=
    (fold.closed i).preimage line.continuous_of_finiteDimensional
  have convex (i : ι) : Convex ℝ (pieces i) := (fold.convex i).affine_preimage line
  have agrees (i : ι) : EqOn (fold.map ∘ line) (maps i) (pieces i) :=
    fun _ hx => fold.map_on_piece i hx
  have covered : Icc (s : ℝ) (t : ℝ) ⊆ ⋃ i, pieces i := by
    intro u hu
    have unit : u ∈ Icc (0 : ℝ) 1 := ⟨s.property.1.trans hu.1, hu.2.trans t.property.2⟩
    have on_segment : line u ∈ segment ℝ x y := by
      rw [← Path.range_segment]
      exact ⟨⟨u, unit⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (inside on_segment)
    exact mem_iUnion.mpr ⟨i, hi⟩
  have speed (i : ι) : ‖(maps i).linear 1‖ ≤ dist x y := by
    have linear : (maps i).linear 1 = fold.place i y - fold.place i x := by
      have h := (maps i).linearMap_vsub (1 : ℝ) 0
      simpa only [vsub_eq_sub, sub_zero, maps, AffineMap.comp_apply,
        line, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero] using h
    rw [linear, ← dist_eq_norm, fold.rigid, dist_comm]
  exact finite_affine_pieces_distance_le pieces closed convex maps (fold.map ∘ line)
    agrees s t (dist x y) ordered covered speed

theorem segmentPath_lipschitz (x y : Plane) (inside : segment ℝ x y ⊆ fold.domain) :
    LipschitzWith (nndist x y) (fold.segmentPath x y inside).curve := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (fold.map (Path.segment x y s)) (fold.map (Path.segment x y t)) ≤ _
  rcases le_total s t with ordered | ordered
  · simpa only [coe_nndist, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ t from ordered)), neg_sub] using
      fold.segment_distance_le x y inside s t ordered
  · rw [dist_comm]
    simpa only [coe_nndist, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ s from ordered))] using
      fold.segment_distance_le x y inside t s ordered

/-- This is the length estimate needed when a planar chord bypasses a vertex. -/
theorem segmentPath_length_le (x y : Plane) (inside : segment ℝ x y ⊆ fold.domain) :
    (fold.segmentPath x y inside).length ≤ edist x y := by
  simpa only [edist_nndist] using (fold.segmentPath x y inside).length_le_of_lipschitz
    (fold.segmentPath_lipschitz x y inside)

end FiniteSurfaceFolding
end SixVertexUnfolding.ConvexPolyhedron
