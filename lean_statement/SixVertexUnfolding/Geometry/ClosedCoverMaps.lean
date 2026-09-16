import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.ContinuousMap.Basic

/-! Glue finitely many continuous maps on closed sets, retaining
their exact values on each original piece. -/

namespace SixVertexUnfolding

open Set

theorem glue_finite_closed_maps {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (pieces : ι → Set X) (closed : ∀ i, IsClosed (pieces i)) (maps : ∀ i, C(pieces i, Y))
    (compatible : ∀ i j (x : X) (hi : x ∈ pieces i) (hj : x ∈ pieces j), maps i ⟨x, hi⟩ = maps j ⟨x, hj⟩) :
    ∃ glued : C((⋃ i, pieces i), Y),
      ∀ i (x : pieces i), glued ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ = maps i x := by
  classical
  let selected (x : ⋃ i, pieces i) := (mem_iUnion.mp x.property).choose
  have selected_mem (x : ⋃ i, pieces i) : x.val ∈ pieces (selected x) :=
    (mem_iUnion.mp x.property).choose_spec
  let glued (x : ⋃ i, pieces i) := maps (selected x) ⟨x.val, selected_mem x⟩
  have agrees (i : ι) (x : ⋃ i, pieces i) (inside : x.val ∈ pieces i) :
      glued x = maps i ⟨x.val, inside⟩ := compatible (selected x) i x.val (selected_mem x) inside
  let cover (i : ι) : Set (⋃ i, pieces i) := {x | x.val ∈ pieces i}
  have covers : ⋃ i, cover i = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨selected x, selected_mem x⟩
  have continuous_piece (i : ι) : ContinuousOn glued (cover i) := by
    apply continuousOn_iff_continuous_restrict.mpr
    have inclusion : Continuous (fun x : cover i => (⟨x.val.val, x.property⟩ : pieces i)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    apply ((maps i).continuous.comp inclusion).congr
    intro x
    exact (agrees i x.val x.property).symm
  exact ⟨⟨glued, (locallyFinite_of_finite cover).continuous covers
    (fun i => (closed i).preimage continuous_subtype_val) continuous_piece⟩,
    fun i x => agrees i ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ x.property⟩

end SixVertexUnfolding
