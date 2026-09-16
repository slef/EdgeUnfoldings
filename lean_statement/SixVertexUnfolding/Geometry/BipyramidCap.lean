import SixVertexUnfolding.Geometry.BipyramidHinges
import SixVertexUnfolding.Geometry.PetalPlacement

/-! Unfold either three-triangle cap with a prescribed rigid base triangle, without overlap. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- Either nonbase triangle in a cap admits a certified outward placement. -/
theorem exists_cap_petal
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (source missing : Fin 3) (different : missing ≠ source)
    (left : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ (B.face triangles upper source).val,
      ∀ y ∈ (B.face triangles upper source).val, dist (left x) (left y) = dist x y) :
    Nonempty (PetalPlacement (B.face triangles upper source) (B.face triangles upper missing)
      (B.equatorVertex source) left) := by
  obtain ⟨k, km, ks, _⟩ := remaining_equator_index missing source different
  have pair : {l : Fin 3 | l ≠ missing} = {k, source} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have vertices : (B.face triangles upper missing).val ∩ (P.vertices : Set Space) =
      {(B.poleVertex upper : Space), (B.equatorVertex k : Space), (B.equatorVertex source : Space)} := by
    rw [B.face_vertices, faceVertices, pair, Set.image_insert_eq, Set.image_singleton]
  exact (B.face triangles upper source).exists_petal_placement (B.face triangles upper missing)
    (B.poleVertex upper) (B.equatorVertex k) (B.equatorVertex source) (B.pole_ne_equator upper k)
    (B.pole_mem_face triangles upper source) ((B.equator_mem_face triangles upper source k).mpr ks)
    vertices (fun member => (B.equator_mem_face triangles upper source source).mp member rfl) left left_rigid

/-- A cap development preserves the base hinges and separates all three original triangles. -/
structure CapPlacement
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (source : Fin 3) where
  place : Fin 3 → Space →ᵃ[ℝ] Plane
  rigid : ∀ i, ∀ x ∈ (B.face triangles upper i).val, ∀ y ∈ (B.face triangles upper i).val,
    dist (place i x) (place i y) = dist x y
  joined : ∀ i, ∀ x : P.Vertex, (x : Space) ∈ (B.face triangles upper i).val →
    (x : Space) ∈ (B.face triangles upper source).val → place i x = place source x
  nonoverlap : ∀ i j, i ≠ j →
    Disjoint (interior (place i '' (B.face triangles upper i).val))
      (interior (place j '' (B.face triangles upper j).val))
  farther : ∀ i, i ≠ source → ∀ x : P.Vertex,
    (x : Space) ∈ (B.face triangles upper source).val →
    (x : Space) ∉ (B.face triangles upper i).val →
    dist (x : Space) (B.equatorVertex source) <
      dist (place source x) (place i (B.equatorVertex source))

/-- Every rigid placement of a cap's base extends to a nonoverlapping placement of the whole cap. -/
theorem exists_cap_placement
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (source : Fin 3) (left : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ (B.face triangles upper source).val,
      ∀ y ∈ (B.face triangles upper source).val, dist (left x) (left y) = dist x y) :
    ∃ cap : B.CapPlacement triangles upper source, cap.place source = left := by
  classical
  let petal (i : Fin 3) (different : i ≠ source) :=
    Classical.choice (B.exists_cap_petal triangles upper source i different left left_rigid)
  let copy (i : Fin 3) := if different : i = source then left else (petal i different).place
  have base_copy : copy source = left := by simp [copy]
  have side_copy (i : Fin 3) (different : i ≠ source) : copy i = (petal i different).place := by simp [copy, different]
  refine ⟨{
    place := copy
    rigid := ?_
    joined := ?_
    nonoverlap := ?_
    farther := ?_
  }, base_copy⟩
  · intro i
    by_cases same : i = source
    · subst i
      simpa only [base_copy] using left_rigid
    · simpa only [side_copy i same] using (petal i same).rigid
  · intro i x xI xB
    rw [base_copy]
    by_cases same : i = source
    · subst i
      rw [base_copy]
    · rw [side_copy i same]
      exact (petal i same).joined x xI xB
  · intro i j different
    by_cases iB : i = source
    · subst i
      rw [base_copy, side_copy j different.symm]
      exact (petal j different.symm).base_safe
    by_cases jB : j = source
    · subst j
      rw [base_copy, side_copy i different]
      exact (petal i different).base_safe.symm
    rw [side_copy i iB, side_copy j jB]
    apply (petal i iB).disjoint (petal j jB)
    intro same
    have indices := B.face_index_injective triangles (a₁ := (upper, i)) (a₂ := (upper, j)) same
    exact different (congrArg Prod.snd indices)
  · intro i different x xB xI
    rw [base_copy, side_copy i different]
    exact (petal i different).farther x xB xI

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
