import SixVertexUnfolding.Geometry.CutTreeWedgeMoves

/-! Finite iteration of the proved expanding-region operation. Coordinates
may change at every step; the conclusion compares all kites in one plane.
This does not construct the cut-surface quotient or its junction data. -/

namespace SixVertexUnfolding.Wedge

open Set

/-- The three geometric facts needed for one step, with its coordinate change. -/
structure RegionStep (before after kite : Set Plane) where
  enlarged : Set Plane
  motion : Plane ≃ᵃⁱ[ℝ] Plane
  contains : before ⊆ enlarged
  avoids : Disjoint enlarged (interior kite)
  updated : motion '' (enlarged ∪ kite) = after

namespace RegionStep

variable {before after kite : Set Plane} (step : RegionStep before after kite)

theorem carries_before : step.motion '' before ⊆ after := by
  exact (image_mono (step.contains.trans subset_union_left)).trans step.updated.subset

theorem carries_kite : step.motion '' kite ⊆ after := by
  exact (image_mono subset_union_right).trans step.updated.subset

include step in
theorem before_avoids : Disjoint before (interior kite) :=
  step.avoids.mono step.contains Subset.rfl

end RegionStep

/-- Map each successive local coordinate plane back to the first one. -/
noncomputable def chainFrame (moves : ℕ → Plane ≃ᵃⁱ[ℝ] Plane) : ℕ → Plane ≃ᵃⁱ[ℝ] Plane
  | 0 => AffineIsometryEquiv.refl ℝ Plane
  | n + 1 => (moves n).symm.trans (chainFrame moves n)

theorem chainFrame_step (moves : ℕ → Plane ≃ᵃⁱ[ℝ] Plane) (n : ℕ) (x : Plane) :
    chainFrame moves (n + 1) (moves n x) = chainFrame moves n x := by
  change chainFrame moves n ((moves n).symm (moves n x)) = chainFrame moves n x
  rw [(moves n).symm_apply_apply]

/-- A finite chain of actual steps separates every earlier closed kite
from the ordinary interior of every later kite in one common plane. -/
theorem finite_chain_separation (n : ℕ) (regions kites : ℕ → Set Plane)
    (steps : ∀ i : Fin n, RegionStep (regions i) (regions (i + 1)) (kites i)) :
    ∃ frames : ℕ → Plane ≃ᵃⁱ[ℝ] Plane,
      frames 0 = AffineIsometryEquiv.refl ℝ Plane ∧
      (∀ i : Fin n, ∀ x, frames (i + 1) ((steps i).motion x) = frames i x) ∧
      (∀ i j : ℕ, i < j → j < n →
        Disjoint (frames i '' kites i) (interior (frames j '' kites j))) ∧
      (∀ j : ℕ, j < n → Disjoint (regions 0) (interior (frames j '' kites j))) ∧
      (∀ i j : ℕ, i ≤ j → j ≤ n → frames i '' regions i ⊆ frames j '' regions j) := by
  classical
  let moves (i : ℕ) : Plane ≃ᵃⁱ[ℝ] Plane :=
    if small : i < n then (steps ⟨i, small⟩).motion else AffineIsometryEquiv.refl ℝ Plane
  let frames := chainFrame moves
  have changes (i : Fin n) (x : Plane) :
      frames (i + 1) ((steps i).motion x) = frames i x := by
    have move_eq : moves i = (steps i).motion := dif_pos i.isLt
    rw [← move_eq]
    exact chainFrame_step moves i x
  let R (i : ℕ) := frames i '' regions i
  let K (i : ℕ) := frames i '' kites i
  have grows (i : ℕ) (small : i < n) : R i ⊆ R (i + 1) := by
    rintro _ ⟨x, member, rfl⟩
    let s := steps ⟨i, small⟩
    exact ⟨s.motion x, s.carries_before ⟨x, member, rfl⟩, changes ⟨i, small⟩ x⟩
  have added (i : ℕ) (small : i < n) : K i ⊆ R (i + 1) := by
    rintro _ ⟨x, member, rfl⟩
    let s := steps ⟨i, small⟩
    exact ⟨s.motion x, s.carries_kite ⟨x, member, rfl⟩, changes ⟨i, small⟩ x⟩
  have avoids (i : ℕ) (small : i < n) : Disjoint (R i) (interior (K i)) := by
    have disjoint := disjoint_image_of_injective (frames i).injective (steps ⟨i, small⟩).before_avoids
    have image_interior : frames i '' interior (kites i) = interior (frames i '' kites i) :=
      (frames i).toHomeomorph.image_interior _
    rw [image_interior] at disjoint
    exact disjoint
  have monotone (i j : ℕ) (order : i ≤ j) (bound : j ≤ n) : R i ⊆ R j := by
    induction j, order using Nat.le_induction with
    | base => exact Subset.rfl
    | succ j order previous =>
      exact (previous (by omega)).trans (grows j (by omega))
  refine ⟨frames, rfl, changes, ?_, ?_, monotone⟩
  · intro i j before small
    exact (avoids j small).mono ((added i (by omega)).trans
      (monotone (i + 1) j before (by omega))) Subset.rfl
  · intro j small
    have start : R 0 = regions 0 := by simp only [R, frames, chainFrame, AffineIsometryEquiv.coe_refl, image_id]
    rw [← start]
    exact (avoids j small).mono (monotone 0 j (by omega) (by omega)) Subset.rfl

/-- Enclose the first kite, carry it through finitely many moves, and
exclude a final kite without requiring a chart beyond that last edge. -/
theorem finite_chain_endpoint_separation (n : ℕ) (regions kites : ℕ → Set Plane)
    (steps : ∀ i : Fin n, RegionStep (regions i) (regions (i + 1)) (kites i))
    (first last : Set Plane) (initial : first ⊆ regions 0)
    (terminal : Disjoint (regions n) (interior last)) :
    ∃ frames : ℕ → Plane ≃ᵃⁱ[ℝ] Plane,
      frames 0 = AffineIsometryEquiv.refl ℝ Plane ∧
      (∀ i : Fin n, ∀ x, frames (i + 1) ((steps i).motion x) = frames i x) ∧
      Disjoint first (interior (frames n '' last)) := by
  obtain ⟨frames, start, compatible, _, _, grows⟩ := finite_chain_separation n regions kites steps
  have first_inside : first ⊆ frames n '' regions n := by
    intro x member
    apply grows 0 n (by omega) le_rfl
    refine ⟨x, initial member, ?_⟩
    rw [start]
    rfl
  have final_avoids := disjoint_image_of_injective (frames n).injective terminal
  have final_interior : frames n '' interior last = interior (frames n '' last) :=
    (frames n).toHomeomorph.image_interior _
  rw [final_interior] at final_avoids
  exact ⟨frames, start, compatible, final_avoids.mono first_inside Subset.rfl⟩

end SixVertexUnfolding.Wedge

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan.WedgeMove

open Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} {fan : JunctionFan T u}
    {incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last}
    {next_chart : P.CutVoronoiChart a (T.vertexTarget (fan.order.neighbors outgoing).val)} {φ : ℝ}
    {next : IncidentTriangles T (fan.order.neighbors outgoing).property.symm next_chart φ} {ω : ℝ}

/-- The constructed geometric move supplies every hypothesis of finite region iteration. -/
def toRegionStep (move : fan.WedgeMove incoming outgoing next ω) :
    RegionStep ((fan.triangles incoming).incomingWedge ω)
      (next.incomingWedge (ω + (fan.triangles outgoing).model.sourceAngle))
      (fan.triangles outgoing).developedKite :=
  ⟨move.enlarged, move.motion, move.contains, move.avoids, move.updated⟩

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan.WedgeMove
