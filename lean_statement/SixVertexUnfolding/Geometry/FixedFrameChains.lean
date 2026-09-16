import SixVertexUnfolding.Geometry.ExpandingRegionChains

/-! Apply the region-chain separation in frames already chosen for the
whole surface. The proof does not select a new development for each pair. -/

namespace SixVertexUnfolding.Wedge

open Set

/-- The endpoint separation holds in any fixed compatible sequence of frames. -/
theorem finite_chain_endpoint_separation_in_frames (n : ℕ) (regions kites : ℕ → Set Plane)
    (steps : ∀ i : Fin n, RegionStep (regions i) (regions (i + 1)) (kites i))
    (frames : ℕ → Plane ≃ᵃⁱ[ℝ] Plane)
    (compatible : ∀ i : Fin n, ∀ x, frames (i + 1) ((steps i).motion x) = frames i x)
    (first last : Set Plane) (initial : first ⊆ regions 0)
    (terminal : Disjoint (regions n) (interior last)) :
    Disjoint (frames 0 '' first) (interior (frames n '' last)) := by
  have grows (i : ℕ) (small : i < n) :
      frames i '' regions i ⊆ frames (i + 1) '' regions (i + 1) := by
    rintro _ ⟨x, member, rfl⟩
    let step := steps ⟨i, small⟩
    exact ⟨step.motion x, step.carries_before ⟨x, member, rfl⟩, compatible ⟨i, small⟩ x⟩
  have propagated (j : ℕ) (bound : j ≤ n) : frames 0 '' first ⊆ frames j '' regions j := by
    induction j with
    | zero => exact image_mono initial
    | succ j previous => exact (previous (by omega)).trans (grows j (by omega))
  have avoids := disjoint_image_of_injective (frames n).injective terminal
  have image_interior : frames n '' interior last = interior (frames n '' last) :=
    (frames n).toHomeomorph.image_interior _
  rw [image_interior] at avoids
  exact avoids.mono (propagated n le_rfl) Subset.rfl

/-- A finite-indexed version uses precisely the frames and steps of the chain. -/
theorem finite_index_chain_endpoint_separation (n : ℕ)
    (regions : Fin (n + 1) → Set Plane) (kites : Fin n → Set Plane)
    (steps : ∀ i : Fin n, RegionStep (regions i.castSucc) (regions i.succ) (kites i))
    (frames : Fin (n + 1) → Plane ≃ᵃⁱ[ℝ] Plane)
    (compatible : ∀ i : Fin n, ∀ x, frames i.succ ((steps i).motion x) = frames i.castSucc x)
    (first last : Set Plane) (initial : first ⊆ regions 0)
    (terminal : Disjoint (regions (Fin.last n)) (interior last)) :
    Disjoint (frames 0 '' first) (interior (frames (Fin.last n) '' last)) := by
  have grows (i : Fin n) :
      frames i.castSucc '' regions i.castSucc ⊆ frames i.succ '' regions i.succ := by
    rintro _ ⟨x, member, rfl⟩
    exact ⟨(steps i).motion x, (steps i).carries_before ⟨x, member, rfl⟩, compatible i x⟩
  have propagated (j : Fin (n + 1)) : frames 0 '' first ⊆ frames j '' regions j := by
    induction j using Fin.induction with
    | zero => exact image_mono initial
    | succ i previous => exact previous.trans (grows i)
  have avoids := disjoint_image_of_injective (frames (Fin.last n)).injective terminal
  have image_interior : frames (Fin.last n) '' interior last =
      interior (frames (Fin.last n) '' last) :=
    (frames (Fin.last n)).toHomeomorph.image_interior _
  rw [image_interior] at avoids
  exact avoids.mono (propagated (Fin.last n)) Subset.rfl

end SixVertexUnfolding.Wedge
