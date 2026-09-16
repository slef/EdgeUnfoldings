import SixVertexUnfolding.Geometry.VertexFanSectorIntersections
import Mathlib.Analysis.Normed.Group.AddCircle

/-! The actual punctured vertex fan has an angular coordinate on a circle
whose circumference is the actual cone angle. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)

/-- Every actual sector has positive angle, so the angular circle has positive length. -/
theorem totalAngle_pos : 0 < fan.totalAngle := by
  apply Finset.sum_pos'
  · intro i _
    exact (fan.sectorAngle_pos i).le
  · exact ⟨0, Finset.mem_univ _, fan.sectorAngle_pos 0⟩

theorem triangle_isCompact (i : Fin n) : IsCompact (fan.triangle i) :=
  (Set.toFinite ({(pole : Space), (fan.neighbor i : Space),
    (fan.neighbor (i + 1) : Space)} : Set Space)).isCompact_convexHull ℝ

/-- Each sector contributes its cumulative starting angle and its ordinary offset. -/
noncomputable def fanCirclePiece (i : Fin n) (x : Space) :
    AddCircle (fan.totalAngle) :=
  (fan.openingAngle 0 i.castSucc + fan.offset i x : ℝ)

/-- The domain excludes just the cone point, where direction is undefined. -/
def fanCircleDomain : Set Space :=
  (⋃ i : Fin n, fan.triangle i) \ {(pole : Space)}

/-- Choose any incident sector containing the point. Agreement is proved below. -/
noncomputable def fanCircleMap (x : Space) : AddCircle (fan.totalAngle) := by
  classical
  exact if h : ∃ i : Fin n, x ∈ fan.triangle i
    then fan.fanCirclePiece h.choose x else 0

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Cumulative angles agree modulo the cone angle at every radial seam. -/
theorem fanCirclePiece_adjacent (i : Fin n) (x : Space)
    (first : x ∈ fan.triangle i)
    (second : x ∈ fan.triangle (i + 1))
    (nonpole : x ≠ pole) :
    fan.fanCirclePiece i x = fan.fanCirclePiece (i + 1) x := by
  obtain ⟨full, zero⟩ := fan.adjacent_sector_offsets small_faces i x first second nonpole
  simp only [fanCirclePiece, full, zero, add_zero]
  have step : fan.openingAngle 0 i.castSucc + fan.sectorAngle i = fan.openingAngle 0 i.succ := by
    have identity := fan.openingAngle_step 0 i
    simp only [zero_add] at identity
    linarith
  rw [step]
  by_cases before : i.val + 1 < n
  · have next : i.succ = (i + 1).castSucc := by
      apply Fin.ext
      exact (Fin.val_add_one_of_lt' before).symm
    rw [next]
  · have last : i.succ = Fin.last n := Fin.ext (by have := i.isLt; simp; omega)
    have wrap : i + 1 = (0 : Fin n) := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Fin.val_zero]
      have count : i.val + 1 = n := by have := i.isLt; omega
      calc
        (i.val + 1 % n) % n = (i.val + 1) % n := by
          simpa only [Nat.mod_eq_of_lt i.isLt] using (Nat.add_mod i.val 1 n).symm
        _ = 0 := by rw [count, Nat.mod_self]
    rw [last, wrap, Fin.castSucc_zero, fan.openingAngle_zero, fan.openingAngle_last,
      AddCircle.coe_period, AddCircle.coe_zero]

include small_faces in
/-- Every possible choice of containing sector gives the same circle point. -/
theorem fanCirclePiece_joined (i j : Fin n) (x : Space)
    (first : x ∈ fan.triangle i)
    (second : x ∈ fan.triangle j) (nonpole : x ≠ pole) :
    fan.fanCirclePiece i x = fan.fanCirclePiece j x := by
  by_cases same : i = j
  · rw [same]
  rcases fan.common_sector_ray small_faces i j same x first second nonpole with h | h
  · obtain ⟨h, _⟩ := h
    subst j
    exact fan.fanCirclePiece_adjacent small_faces i x first second nonpole
  · obtain ⟨h, _⟩ := h
    subst i
    exact (fan.fanCirclePiece_adjacent small_faces j x second first nonpole).symm

include small_faces in
theorem fanCircleMap_on_sector (i : Fin n) (x : Space)
    (member : x ∈ fan.triangle i) (nonpole : x ≠ pole) :
    fan.fanCircleMap x = fan.fanCirclePiece i x := by
  classical
  rw [fanCircleMap, dif_pos ⟨i, member⟩]
  exact fan.fanCirclePiece_joined small_faces _ i x
    (Exists.choose_spec (⟨i, member⟩ : ∃ j : Fin n, x ∈ fan.triangle j))
    member nonpole

/-- Each sector formula is continuous away from the pole. -/
theorem fanCirclePiece_continuousAt (i : Fin n) (x : Space)
    (nonpole : x ≠ pole) : ContinuousAt (fan.fanCirclePiece i) x := by
  have angle_continuous : ContinuousAt (fun y : Space => fan.offset i y) x :=
    (EuclideanGeometry.continuousAt_angle
      (x := ((fan.neighbor i : Space), (pole : Space), x))
      (fan.neighbor_ne_pole i) nonpole).comp
      (f := fun y : Space => ((fan.neighbor i : Space),
        (pole : Space), y))
      (show ContinuousAt (fun y : Space => ((fan.neighbor i : Space),
        (pole : Space), y)) x by fun_prop)
  exact (AddCircle.continuous_mk' (fan.totalAngle)).continuousAt.comp
    (continuousAt_const.add angle_continuous)

include small_faces in
/-- The sector formulas paste to one continuous angular coordinate on the actual fan. -/
theorem fanCircleMap_continuousOn :
    ContinuousOn (fan.fanCircleMap) (fan.fanCircleDomain) := by
  rw [continuousOn_iff_continuous_restrict]
  let pieces (i : Fin n) : Set (fan.fanCircleDomain) :=
    {x | (x : Space) ∈ fan.triangle i}
  have closed (i : Fin n) : IsClosed (pieces i) :=
    (fan.triangle_isCompact _).isClosed.preimage continuous_subtype_val
  have covers : (univ : Set (fan.fanCircleDomain)) = ⋃ i, pieces i := by
    ext x
    constructor
    · intro _
      obtain ⟨i, hi⟩ := mem_iUnion.mp x.property.1
      exact mem_iUnion.mpr ⟨i, hi⟩
    · intro _
      trivial
  rw [← continuousOn_univ, covers]
  apply (locallyFinite_of_finite pieces).continuousOn_iUnion closed
  intro i
  have formula : Continuous (fun x : fan.fanCircleDomain => fan.fanCirclePiece i x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (fan.fanCirclePiece_continuousAt i x x.property.2).comp continuous_subtype_val.continuousAt
  exact formula.continuousOn.congr (fun x hx => fan.fanCircleMap_on_sector small_faces i x hx x.property.2)

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
