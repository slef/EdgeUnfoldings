import SixVertexUnfolding.Geometry.StarDevelopmentMap

/-! All inverse branches of the actual global development use one
finite family of rigid maps, inherited from its radial triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

theorem finite_inverse_pieces :
    ∃ maps : Set (Plane →ᵃ[ℝ] Space), maps.Finite ∧ (∀ g ∈ maps, Isometry g) ∧
      ∀ b : frontier P.body, ∃ g ∈ maps, (b : Space) = g (charts.develop b) := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  letI : DecidableRel T.graph.Adj := Classical.decRel _
  let pieces (i : T.graph.Dart × Bool) :=
    (((charts.global i.1.adj).sideTriangle i.2).rigid_pieces).choose
  have specs (i : T.graph.Dart × Bool) :=
    (((charts.global i.1.adj).sideTriangle i.2).rigid_pieces).choose_spec
  refine ⟨⋃ i, pieces i, finite_iUnion (fun i => (specs i).1), ?_, ?_⟩
  · intro g member
    obtain ⟨i, member⟩ := mem_iUnion.mp member
    exact (specs i).2.1 g member
  · intro b
    obtain ⟨u, v, edge, side, inside, at_b⟩ := charts.develop_spec b
    let i : T.graph.Dart × Bool := (⟨(u, v), edge⟩, side)
    let H := (charts.global edge).sideTriangle side
    obtain ⟨g, member, formula⟩ := (specs i).2.2 (H.homeomorph ⟨b, inside⟩)
    refine ⟨g, mem_iUnion.mpr ⟨i, member⟩, ?_⟩
    change ((H.homeomorph.symm (H.homeomorph ⟨b, inside⟩)).val : Space) = g (H.homeomorph ⟨b, inside⟩) at formula
    rw [H.homeomorph.symm_apply_apply, at_b] at formula
    exact formula

/-- Every genuine right inverse retains these same finite rigid formulas. -/
theorem inverse_has_finite_pieces (region : Set Plane) (inverse : region → frontier P.body)
    (right_inverse : ∀ x, charts.develop (inverse x) = x.val) :
    HasFiniteRigidPieces region (fun x => (inverse x : Space)) := by
  obtain ⟨maps, finite_maps, rigid, selected⟩ := charts.finite_inverse_pieces
  refine ⟨maps, finite_maps, rigid, ?_⟩
  intro x
  obtain ⟨g, member, formula⟩ := selected (inverse x)
  exact ⟨g, member, formula.trans (congrArg g (right_inverse x))⟩

end SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts
