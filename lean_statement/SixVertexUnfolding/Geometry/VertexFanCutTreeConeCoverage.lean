import SixVertexUnfolding.Geometry.VertexFanCutEdgeCircles
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeSmallLinks
import SixVertexUnfolding.Geometry.CutTreeAngleAccounting
import SixVertexUnfolding.Geometry.VertexFanCircleCoverage
import SixVertexUnfolding.Geometry.CircleCoverLength

/-! The actual triangles incident to an original tree vertex cover its
entire cone angle. This discharges the local geometric budget obligation. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set EuclideanGeometry

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n) (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- At an original vertex the actual incident triangle corners cover the full cone angle. -/
theorem incident_triangle_angles_cover_cone (a : frontier P.body) (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (triangles : (d : T.graph.Dart) → CutEdgeTriangles T d.adj)
    (u : T.vertices) (at_vertex : (u : Space) = (pole : Space)) :
    fan.totalAngle ≤ T.incidentAngleSum (fun d => (triangles d).model) u := by
  classical
  letI : Fact (0 < fan.totalAngle) := ⟨fan.totalAngle_pos⟩
  let D (v : T.graph.neighborSet u) := triangles (T.graph.dartOfNeighborSet u v)
  choose radius positive arcs using fun v : T.graph.neighborSet u =>
    fan.cut_edge_corner_circle_arcs small_faces (D v) at_vertex
  obtain ⟨ε, ep, cone_link⟩ := fan.fanCircleMap_small_link_surjective size small_faces
  obtain ⟨δ, dp, triangle_link⟩ := small_incident_triangles_cover_small_links size small_faces a T triangles u
  let V : Set ℝ := Iio ε ∩ Iio δ ∩ ⋂ v : T.graph.neighborSet u, Iio (radius v)
  have openV : IsOpen V := (isOpen_Iio.inter isOpen_Iio).inter
    (isOpen_iInter_of_finite (fun _ => isOpen_Iio))
  have zeroV : (0 : ℝ) ∈ V := ⟨⟨ep, dp⟩, mem_iInter.mpr positive⟩
  obtain ⟨R, Rp, ballV⟩ := Metric.isOpen_iff.mp openV 0 zeroV
  let ρ := R / 2
  have ρp : 0 < ρ := by dsimp [ρ]; positivity
  have small : ρ ∈ V := ballV (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ρp]; dsimp [ρ]; linarith)
  choose f g boundedf boundedg coversf coversg using fun v : T.graph.neighborSet u =>
    arcs v ρ ⟨ρp, mem_iInter.mp small.2 v⟩
  let width : (T.graph.neighborSet u ⊕ T.graph.neighborSet u) → ℝ := Sum.elim
    (fun v => angle (D v).model.first (D v).model.left (D v).model.right)
    (fun v => angle (D v).model.second (D v).model.left (D v).model.right)
  let maps : (T.graph.neighborSet u ⊕ T.graph.neighborSet u) → ℝ → AddCircle (fan.totalAngle) :=
    Sum.elim f g
  have covered : ∀ z : AddCircle (fan.totalAngle), ∃ i, z ∈ maps i '' Icc (0 : ℝ) (width i) := by
    intro z
    obtain ⟨x, _, sphere, at_z⟩ := cone_link ρ ⟨ρp, small.1.1⟩ z
    obtain ⟨v, edge, first | second⟩ := triangle_link ρ ⟨ρp, small.1.2⟩ x
      (by rw [at_vertex]; exact sphere)
    · obtain ⟨q, hq, folded⟩ := first
      refine ⟨Sum.inl ⟨v, edge⟩, ?_⟩
      have member := coversf ⟨v, edge⟩ q hq
      have folded_space : ((D ⟨v, edge⟩).first_triangle.homeomorph.symm q).val.val = (x : Space) :=
        congrArg Subtype.val folded
      rw [folded_space, at_z] at member
      exact member
    · obtain ⟨q, hq, folded⟩ := second
      refine ⟨Sum.inr ⟨v, edge⟩, ?_⟩
      have member := coversg ⟨v, edge⟩ q hq
      have folded_space : ((D ⟨v, edge⟩).second_triangle.homeomorph.symm q).val.val = (x : Space) :=
        congrArg Subtype.val folded
      rw [folded_space, at_z] at member
      exact member
  have bound := circle_cover_length (fan.totalAngle) maps (fun _ => 0) width
    (by intro i; cases i <;> exact angle_nonneg _ _ _)
    (by intro i; cases i with | inl v => exact boundedf v | inr v => exact boundedg v)
    covered
  simpa only [sub_zero, Fintype.sum_sum_type, width, Sum.elim_inl, Sum.elim_inr,
    ← Finset.sum_add_distrib, CutLocusTree.incidentAngleSum, D] using bound

include size small_faces in
/-- The inequality is independent of all choices of planar metric model. -/
theorem incident_model_angles_cover_cone (a : frontier P.body) (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)
    (u : T.vertices) (at_vertex : (u : Space) = (pole : Space)) :
    fan.totalAngle ≤ T.incidentAngleSum models u := by
  classical
  let triangles (d : T.graph.Dart) := Classical.choice (small_exists_cut_edge_triangles size small_faces a T d.adj)
  have bound := fan.incident_triangle_angles_cover_cone size small_faces a T triangles u at_vertex
  have same : T.incidentAngleSum (fun d => (triangles d).model) u = T.incidentAngleSum models u := by
    apply Finset.sum_congr rfl
    intro v _
    have angles := ((triangles (T.graph.dartOfNeighborSet u v)).model).same_edge_corner_angles
      (models (T.graph.dartOfNeighborSet u v))
    exact congrArg₂ (· + ·) angles.1 angles.2
  exact bound.trans_eq same

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
