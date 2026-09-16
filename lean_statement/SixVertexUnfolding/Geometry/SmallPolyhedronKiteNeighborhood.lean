import SixVertexUnfolding.Geometry.KiteNeighborhood
import SixVertexUnfolding.Geometry.SmallPolyhedronKiteLocalInverse
import SixVertexUnfolding.Geometry.SmallPolyhedronStarInversePatchMetric

/-! A retained point in a kite interior has a planar disk on which
the constructed folding is the true inverse of the star development.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- A planar disk around an interior kite point has a continuous actual inverse. -/
theorem small_exists_kite_inverse_disk {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (b : P.UncutSurface a)
    (inside : charts.develop b.val ∈ interior (charts.kite edge)) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ inverse : C(Metric.ball (charts.develop b.val) radius, P.UncutSurface a),
      HasFiniteRigidPieces (Metric.ball (charts.develop b.val) radius) (fun x => ((inverse x).val : Space)) ∧
      (∀ x, charts.develop (inverse x).val = x.val) ∧
      (∀ (c : P.UncutSurface a) (member : charts.develop c.val ∈ Metric.ball (charts.develop b.val) radius),
        inverse ⟨charts.develop c.val, member⟩ = c) := by
  obtain ⟨fold⟩ := (charts.global edge).exists_folding
  let x : (charts.global edge).kite := ⟨charts.develop b.val, interior_subset inside⟩
  have outside : fold.map x ∉ P.starCuts a := by
    obtain ⟨w, z, other, actual⟩ := charts.develop_spec b.val
    by_cases same : s(u, v) = s(w, z)
    · have matching : (charts.global edge).Places b.val x.val := by
        rcases Sym2.eq_iff.mp same with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact actual
        · exact (charts.places_reverse other b.val _).mp actual
      have recovered := fold.map_of_placement matching
      rw [recovered]
      exact b.property
    · have excluded := separated other edge (Ne.symm same)
      exact (disjoint_left.mp excluded ((charts.global other).places_mem_kite actual) inside).elim
  obtain ⟨radius, positive, contained, uncut⟩ := fold.exists_uncut_disk x inside outside
  let inverse : C(Metric.ball x.val radius, P.UncutSurface a) :=
    ⟨fun y => ⟨fold.map ⟨y, contained y.property⟩, uncut y⟩,
      (fold.map.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  refine ⟨radius, positive, inverse, ?_, ?_, ?_⟩
  · obtain ⟨maps, finite_maps, rigid, selected⟩ := fold.rigid_pieces
    exact ⟨maps, finite_maps, rigid, fun y => selected ⟨y, contained y.property⟩⟩
  · intro y
    exact small_develop_kite_fold size small_faces charts cofacial edge fold ⟨y, contained y.property⟩ (uncut y)
  · intro c member
    apply Subtype.ext
    exact small_kite_fold_left_inverse size small_faces charts separated cofacial edge fold
      (Metric.ball x.val radius) Metric.isOpen_ball contained uncut c member

end SixVertexUnfolding.ConvexPolyhedron
