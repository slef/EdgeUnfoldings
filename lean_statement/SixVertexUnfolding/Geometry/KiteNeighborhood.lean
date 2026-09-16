import SixVertexUnfolding.Geometry.KiteLocalInverse
import SixVertexUnfolding.Geometry.StarInversePatchMetric

/-! A retained point in a kite interior has a planar disk on which
the constructed folding is the true inverse of the star development. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

namespace PlacedCutEdgeTriangles.Folding

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} {D : PlacedCutEdgeTriangles T edge} (fold : D.Folding)

theorem exists_uncut_disk (x : D.kite) (inside : x.val ∈ interior D.kite)
    (outside : fold.map x ∉ P.starCuts a) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ contained : Metric.ball x.val radius ⊆ D.kite,
      ∀ y : Metric.ball x.val radius, fold.map ⟨y, contained y.property⟩ ∉ P.starCuts a := by
  have near : ∀ᶠ y in 𝓝 x, fold.map y ∉ P.starCuts a :=
    fold.map.continuous.continuousAt.preimage_mem_nhds
      ((P.starCuts_closed a).isOpen_compl.mem_nhds outside)
  obtain ⟨ε, positive, uncut⟩ := Metric.eventually_nhds_iff.mp near
  obtain ⟨δ, δ_positive, disk⟩ := Metric.isOpen_iff.mp isOpen_interior x.val inside
  let radius := min ε δ
  have contained : Metric.ball x.val radius ⊆ D.kite := by
    intro y hy
    exact interior_subset (disk ((Metric.mem_ball).mp hy |>.trans_le (min_le_right _ _)))
  refine ⟨radius, lt_min positive δ_positive, contained, ?_⟩
  intro y
  apply uncut
  exact (Metric.mem_ball.mp y.property).trans_le (min_le_left _ _)

end PlacedCutEdgeTriangles.Folding

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- A planar disk around an interior kite point has a continuous actual inverse. -/
theorem exists_kite_inverse_disk {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
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
    · have excluded := graph.global_kites_nonoverlap small_faces T charts source at_source other edge (Ne.symm same)
      exact (disjoint_left.mp excluded ((charts.global other).places_mem_kite actual) inside).elim
  obtain ⟨radius, positive, contained, uncut⟩ := fold.exists_uncut_disk x inside outside
  let inverse : C(Metric.ball x.val radius, P.UncutSurface a) :=
    ⟨fun y => ⟨fold.map ⟨y, contained y.property⟩, uncut y⟩,
      (fold.map.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  refine ⟨radius, positive, inverse, ?_, ?_, ?_⟩
  · obtain ⟨maps, finite_maps, rigid, selected⟩ := fold.rigid_pieces
    exact ⟨maps, finite_maps, rigid, fun y => selected ⟨y, contained y.property⟩⟩
  · intro y
    exact graph.develop_kite_fold small_faces charts cofacial edge fold ⟨y, contained y.property⟩ (uncut y)
  · intro c member
    apply Subtype.ext
    exact graph.kite_fold_left_inverse small_faces charts source at_source cofacial edge fold
      (Metric.ball x.val radius) Metric.isOpen_ball contained uncut c member

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
