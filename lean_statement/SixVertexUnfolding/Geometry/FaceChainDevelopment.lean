import SixVertexUnfolding.Geometry.PolygonPetal

/-! Develop a finite chronological chain of whole faces. Each next face is
placed outward across its original hinge; a repeated face keeps its placement. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron}

/-- The outward side condition for a whole pair of joined facets. -/
def OutwardFacePlacement (F G : P.Face) (left right : Space →ᵃ[ℝ] Plane) : Prop :=
  P.ShareEdge F G → ∀ p ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space),
    ∀ q ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space), p ≠ q →
    ∀ x ∈ F.val, ∀ y ∈ G.val, OppositeHingeSides (left p) (left q) (left x) (right y)

/-- Extend a rigid placement by one adjacent face, or keep it for a repeated face. -/
theorem extend_face_placement (F G : P.Face) (adjacent : F = G ∨ P.ShareEdge F G)
    (left : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y) :
    ∃ right : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ G.val, ∀ y ∈ G.val, dist (right x) (right y) = dist x y) ∧
      EqOn left right (F.val ∩ G.val) ∧ OutwardFacePlacement F G left right := by
  rcases adjacent with rfl | shared
  · exact ⟨left, rigid, fun _ _ => rfl, fun impossible => (F.shareEdge_irrefl impossible).elim⟩
  · obtain ⟨right, right_rigid, joined, _, _, outward⟩ := F.exists_polygon_petal G shared left rigid
    exact ⟨right, right_rigid, joined, fun _ => outward⟩

/-- Rigid placements of a finite face chain, joined outward at every step. -/
structure FaceChainDevelopment {n : ℕ} (face : Fin (n + 1) → P.Face) where
  place : Fin (n + 1) → Space →ᵃ[ℝ] Plane
  rigid : ∀ i, ∀ x ∈ (face i).val, ∀ y ∈ (face i).val,
    dist (place i x) (place i y) = dist x y
  joined : ∀ i : Fin n, EqOn (place i.castSucc) (place i.succ)
    ((face i.castSucc).val ∩ (face i.succ).val)
  outward : ∀ i : Fin n, OutwardFacePlacement (face i.castSucc) (face i.succ)
    (place i.castSucc) (place i.succ)

/-- Every finite adjacent face chain has a coherent outward development. -/
theorem exists_face_chain_development {n : ℕ} (face : Fin (n + 1) → P.Face)
    (adjacent : ∀ i : Fin n, face i.castSucc = face i.succ ∨ P.ShareEdge (face i.castSucc) (face i.succ)) :
    Nonempty (FaceChainDevelopment face) := by
  induction n with
  | zero =>
      obtain ⟨place, rigid⟩ := (face 0).exists_rigid_placement
      refine ⟨⟨fun _ => place, ?_, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩
      intro i
      have same : i = 0 := Fin.ext (by omega)
      simpa only [same] using rigid
  | succ n ih =>
      let previous : Fin (n + 1) → P.Face := fun i => face i.castSucc
      obtain ⟨old⟩ := ih previous (fun i => adjacent i.castSucc)
      obtain ⟨right, right_rigid, joined, outward⟩ := extend_face_placement
        (face (Fin.last n).castSucc) (face (Fin.last (n + 1))) (adjacent (Fin.last n))
        (old.place (Fin.last n)) (old.rigid (Fin.last n))
      let place : Fin (n + 1 + 1) → Space →ᵃ[ℝ] Plane := Fin.lastCases right old.place
      refine ⟨⟨place, ?_, ?_, ?_⟩⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [place, Fin.lastCases_last] using right_rigid
        · simpa only [place, Fin.lastCases_castSucc, previous] using old.rigid j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [place, Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc] using joined
        · simpa only [place, Fin.succ_castSucc, Fin.lastCases_castSucc, previous] using old.joined j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [place, Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc] using outward
        · simpa only [place, Fin.succ_castSucc, Fin.lastCases_castSucc, previous] using old.outward j

/-- The same development statement for any positive number of faces. -/
theorem exists_ordered_face_development {n : ℕ} (positive : 0 < n) (face : Fin n → P.Face)
    (adjacent : ∀ i j, i.val + 1 = j.val → face i = face j ∨ P.ShareEdge (face i) (face j)) :
    ∃ place : Fin n → Space →ᵃ[ℝ] Plane,
      (∀ i, ∀ x ∈ (face i).val, ∀ y ∈ (face i).val, dist (place i x) (place i y) = dist x y) ∧
      (∀ i j, i.val + 1 = j.val → EqOn (place i) (place j) ((face i).val ∩ (face j).val)) ∧
      (∀ i j, i.val + 1 = j.val → OutwardFacePlacement (face i) (face j) (place i) (place j)) := by
  cases n with
  | zero => omega
  | succ n =>
      obtain ⟨net⟩ := exists_face_chain_development face (fun i => adjacent i.castSucc i.succ rfl)
      refine ⟨net.place, net.rigid, ?_, ?_⟩
      · intro i j next
        let k : Fin n := ⟨i.val, by omega⟩
        have first : i = k.castSucc := Fin.ext rfl
        have second : j = k.succ := Fin.ext next.symm
        rw [first, second]
        exact net.joined k
      · intro i j next
        let k : Fin n := ⟨i.val, by omega⟩
        have first : i = k.castSucc := Fin.ext rfl
        have second : j = k.succ := Fin.ext next.symm
        rw [first, second]
        exact net.outward k

end SixVertexUnfolding.ConvexPolyhedron
