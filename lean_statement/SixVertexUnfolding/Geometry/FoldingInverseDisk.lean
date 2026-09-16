import SixVertexUnfolding.Geometry.KiteLocalInverse

/-! An actual continuous finite folding around a retained point gives
a true inverse disk for the global development. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Filter Topology

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

theorem exists_folding_inverse_disk {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (region : Set Plane) (fold : C(region, frontier P.body))
    (pieces : HasFiniteRigidPieces region (fun x => (fold x : Space)))
    (center : region) (inside : center.val ∈ interior region) (outside : fold center ∉ P.starCuts a)
    (develops : ∀ x : region, fold x ∉ P.starCuts a → charts.develop (fold x) = x.val) :
    ∃ radius > 0, ∃ inverse : C(Metric.ball center.val radius, P.UncutSurface a),
      HasFiniteRigidPieces (Metric.ball center.val radius) (fun x => ((inverse x).val : Space)) ∧
      (∀ x, charts.develop (inverse x).val = x.val) ∧
      (∀ (b : P.UncutSurface a) (member : charts.develop b.val ∈ Metric.ball center.val radius),
        inverse ⟨charts.develop b.val, member⟩ = b) := by
  have near : ∀ᶠ y in 𝓝 center, fold y ∉ P.starCuts a :=
    fold.continuous.continuousAt.preimage_mem_nhds
      ((P.starCuts_closed a).isOpen_compl.mem_nhds outside)
  obtain ⟨ε, ep, uncut⟩ := Metric.eventually_nhds_iff.mp near
  obtain ⟨δ, dp, disk⟩ := Metric.isOpen_iff.mp isOpen_interior center.val inside
  let radius := min ε δ
  have contained : Metric.ball center.val radius ⊆ region := fun y hy =>
    interior_subset (disk ((Metric.mem_ball.mp hy).trans_le (min_le_right _ _)))
  have retained (y : Metric.ball center.val radius) : fold ⟨y, contained y.property⟩ ∉ P.starCuts a :=
    uncut ((Metric.mem_ball.mp y.property).trans_le (min_le_left _ _))
  let inverse : C(Metric.ball center.val radius, P.UncutSurface a) :=
    ⟨fun y => ⟨fold ⟨y, contained y.property⟩, retained y⟩,
      (fold.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  have right_inverse (y : Metric.ball center.val radius) : charts.develop (inverse y).val = y.val :=
    develops ⟨y, contained y.property⟩ (retained y)
  refine ⟨radius, lt_min ep dp, inverse, ?_, right_inverse, ?_⟩
  · obtain ⟨maps, finite_maps, rigid, selected⟩ := pieces
    exact ⟨maps, finite_maps, rigid, fun y => selected ⟨y, contained y.property⟩⟩
  · let development : C(P.UncutSurface a, Plane) :=
      ⟨fun b => charts.develop b.val, graph.develop_continuous small_faces charts cofacial⟩
    exact local_inverse_of_dense_unique development charts.triangleInteriorPoints
      (graph.triangle_interior_points_dense small_faces charts)
      (graph.develop_unique_on_dense_interiors small_faces charts source at_source cofacial)
      (Metric.ball center.val radius) Metric.isOpen_ball inverse right_inverse

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
