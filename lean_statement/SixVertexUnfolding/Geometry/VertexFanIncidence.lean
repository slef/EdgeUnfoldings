import SixVertexUnfolding.Geometry.VertexFanAngles

/-! The local cycle lists each incident original face exactly once.
This identifies its angle sum with all actual sectors at the vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n) (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Distinct sectors are portions of distinct original faces. -/
theorem faces_injective : Function.Injective fan.face := by
  classical
  intro i j same
  have pairs : ({i, i + 1} : Finset (Fin n)) = {j, j + 1} := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [← fan.neighbor_mem_face_iff small_faces i k,
      ← fan.neighbor_mem_face_iff small_faces j k, same]
  have bounds := fan.sector_count_bounds size
  have first : i = j ∨ i = j + 1 := by
    have member : i ∈ ({j, j + 1} : Finset (Fin n)) := pairs ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using member
  have second : i + 1 = j ∨ i + 1 = j + 1 := by
    have member : i + 1 ∈ ({j, j + 1} : Finset (Fin n)) := pairs ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using member
  rcases first with equal | forward
  · exact equal
  rcases second with backward | parallel
  · have zero : (0 : Fin n) = 1 + 1 := add_left_cancel (show j + 0 = j + (1 + 1) by
      rw [add_zero, ← add_assoc, ← forward, backward])
    have values := congrArg Fin.val zero
    change 0 = (1 % n + 1 % n) % n at values
    simp only [Nat.mod_eq_of_lt (show 1 < n by omega),
      show 1 + 1 = 2 from rfl, Nat.mod_eq_of_lt (show 2 < n by omega)] at values
    omega
  · exact add_right_cancel parallel

include fan size small_faces in
/-- There are exactly as many incident faces as sectors in this cycle. -/
theorem incident_face_count : Nat.card {F : P.Face // (pole : Space) ∈ F.val} = n := by
  let index : Fin n → {F : P.Face // (pole : Space) ∈ F.val} :=
    fun i => ⟨fan.face i, fan.pole_mem i⟩
  have injective : Function.Injective index := by
    intro i j same
    exact fan.faces_injective size small_faces (congrArg Subtype.val same)
  have surjective : Function.Surjective index := by
    intro F
    obtain ⟨i, same⟩ := (fan.covers small_faces F.val).mp F.property
    exact ⟨i, Subtype.ext same⟩
  simpa only [Nat.card_fin] using (Nat.card_congr (Equiv.ofBijective index ⟨injective, surjective⟩)).symm

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
