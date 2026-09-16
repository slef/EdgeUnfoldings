import SixVertexUnfolding.OctahedralFans

/-! The seven retained hinges of the eight-triangle fan-and-petal development. -/

namespace SixVertexUnfolding.OctahedralNet

open OctahedralTriangles

/-- `false` names a fan triangle; `true` names its attached petal. -/
abbrev FaceIndex := Bool × Fin 4

/-- Three consecutive fan hinges and four fan-to-petal hinges. -/
def hinges : SimpleGraph FaceIndex where
  Adj x y :=
    (x.1 = false ∧ y.1 = false ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
    (x.1 ≠ y.1 ∧ x.2 = y.2)
  symm := by
    rintro x y (⟨hx, hy, before | after⟩ | ⟨opposite, same⟩)
    · exact Or.inl ⟨hy, hx, Or.inr before⟩
    · exact Or.inl ⟨hy, hx, Or.inl after⟩
    · exact Or.inr ⟨opposite.symm, same.symm⟩
  loopless := ⟨by
    intro x adjacent
    rcases adjacent with ⟨_, _, bad⟩ | ⟨bad, _⟩
    · omega
    · exact bad rfl⟩

instance : DecidableRel hinges.Adj := by unfold hinges; infer_instance

theorem connected : hinges.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨(false, 0), ?_⟩
  have step01 : hinges.Adj (false, 0) (false, 1) := by decide
  have step12 : hinges.Adj (false, 1) (false, 2) := by decide
  have step23 : hinges.Adj (false, 2) (false, 3) := by decide
  have fan_reachable (i : Fin 4) : hinges.Reachable (false, 0) (false, i) := by
    fin_cases i
    · exact SimpleGraph.Reachable.rfl
    · exact step01.reachable
    · exact step01.reachable.trans step12.reachable
    · exact (step01.reachable.trans step12.reachable).trans step23.reachable
  rintro ⟨petal, i⟩
  cases petal
  · exact fan_reachable i
  · exact (fan_reachable i).trans ((show hinges.Adj (false, i) (true, i) from Or.inr ⟨by change false ≠ true; decide, rfl⟩).reachable)

/-- The prescribed seven hinges form a tree on all eight triangles. -/
theorem isTree : hinges.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  decide

/-- The underlying original subdivision triangle at each position in the opening. -/
def triangle (source : Fin 6) (slit : Fin 4) (index : FaceIndex) : Fin 8 :=
  if index.1 then fanTriangle source (slit + index.2) else fanTriangle (opposite source) (slit + index.2)

theorem triangle_bijective : ∀ source slit, Function.Bijective (triangle source slit) := by decide

theorem vertices_injective : Function.Injective OctahedralTriangles.vertices := by decide

theorem octahedron_carrier : ∀ t, carrier .octahedron t = OctahedralTriangles.vertices t := by decide

/-- Every retained hinge is one of the seven construction steps, in one of its two directions. -/
theorem hinge_cases : ∀ x y, hinges.Adj x y →
    (∃ i : Fin 3, x = (false, i.castSucc) ∧ y = (false, i.succ)) ∨
    (∃ i : Fin 3, y = (false, i.castSucc) ∧ x = (false, i.succ)) ∨
    (∃ i : Fin 4, x = (false, i) ∧ y = (true, i)) ∨
    (∃ i : Fin 4, y = (false, i) ∧ x = (true, i)) := by decide

/-- Consecutive fan triangles share precisely the indicated pole-to-equator pair. -/
theorem fan_common_vertices : ∀ source slit (i : Fin 3),
    OctahedralTriangles.vertices (triangle source slit (false, i.castSucc)) ∩
      OctahedralTriangles.vertices (triangle source slit (false, i.succ)) =
        {opposite source, fanNeighbor (opposite source) ((slit + i.castSucc) + 1)} := by decide

/-- A fan triangle and its petal share precisely their equator pair. -/
theorem petal_common_vertices : ∀ source slit i,
    OctahedralTriangles.vertices (triangle source slit (false, i)) ∩
      OctahedralTriangles.vertices (triangle source slit (true, i)) =
        {fanNeighbor source (slit + i), fanNeighbor source ((slit + i) + 1)} := by decide

/-- All seven retained hinges have exactly two common distinct original vertex labels. -/
theorem hinge_common_card : ∀ source slit x y, hinges.Adj x y →
    (OctahedralTriangles.vertices (triangle source slit x) ∩
      OctahedralTriangles.vertices (triangle source slit y)).card = 2 := by decide

end SixVertexUnfolding.OctahedralNet
