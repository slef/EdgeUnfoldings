import SixVertexUnfolding.Geometry.CutEdgeCornerAngles
import SixVertexUnfolding.Geometry.JunctionAngleSum
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! An exact angle identity for all metric triangles of the cut tree.
Each directed edge contributes one source angle. The vertex term sums
both incident corners. Identifying cone-vertex sums remains geometric work. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutLocusTree

open Real Set EuclideanGeometry
open scoped BigOperators

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)
  [Fintype T.vertices] [DecidableRel T.graph.Adj]
  (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

/-- The actual triangle corners incident to a tree vertex. -/
noncomputable def incidentAngleSum (u : T.vertices) : ℝ :=
  ∑ v : T.graph.neighborSet u,
    let M := models (T.graph.dartOfNeighborSet u v)
    angle M.first M.left M.right + angle M.second M.left M.right

private theorem sum_darts (f : T.graph.Dart → ℝ) :
    ∑ d, f d = ∑ u, ∑ v : T.graph.neighborSet u, f (T.graph.dartOfNeighborSet u v) := by
  let e : (Σ u, T.graph.neighborSet u) ≃ T.graph.Dart := {
    toFun := fun s => T.graph.dartOfNeighborSet s.1 s.2
    invFun := fun d => ⟨d.fst, d.snd, d.adj⟩
    left_inv := by rintro ⟨u, v, edge⟩; rfl
    right_inv := by rintro ⟨⟨u, v⟩, edge⟩; rfl }
  have reindexed := (Equiv.sum_comp e f).symm
  rwa [Fintype.sum_sigma] at reindexed

/-- The sum of all triangle angles, with opposite orientations identified. -/
theorem sum_source_and_vertex_angles :
    (∑ d, (models d).sourceAngle) + (∑ u, T.incidentAngleSum models u) =
          2 * (Fintype.card T.vertices : ℝ) * π - 2 * π := by
  classical
  dsimp only [incidentAngleSum]
  let left (d : T.graph.Dart) := angle (models d).first (models d).left (models d).right
  let right (d : T.graph.Dart) := angle (models d).first (models d).right (models d).left
  let reverse : T.graph.Dart ≃ T.graph.Dart := {
    toFun := SimpleGraph.Dart.symm
    invFun := SimpleGraph.Dart.symm
    left_inv := SimpleGraph.Dart.symm_symm
    right_inv := SimpleGraph.Dart.symm_symm }
  have at_reverse (d : T.graph.Dart) : right d = left (reverse d) :=
    ((models d).reverse_angles (models d.symm)).2.2
  have reversed : ∑ d, right d = ∑ d, left d := by
    simp_rw [at_reverse]
    exact Equiv.sum_comp reverse left
  have corners :
      (∑ u, ∑ v : T.graph.neighborSet u,
        let M := models (T.graph.dartOfNeighborSet u v)
        angle M.first M.left M.right + angle M.second M.left M.right) = 2 * ∑ d, left d := by
    rw [← T.sum_darts (fun d => angle (models d).first (models d).left (models d).right +
      angle (models d).second (models d).left (models d).right)]
    have paired (d : T.graph.Dart) :
        angle (models d).first (models d).left (models d).right +
          angle (models d).second (models d).left (models d).right = 2 * left d := by
      rw [← (models d).paired_corner_angles.1]
      exact (two_mul _).symm
    simp_rw [paired]
    exact (Finset.mul_sum _ _ _).symm
  have triangles :
      (∑ d, (models d).sourceAngle) + (∑ d, left d) + (∑ d, right d) =
        (Fintype.card T.graph.Dart : ℝ) * π := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have each (d : T.graph.Dart) : (models d).sourceAngle + left d + right d = π :=
      (models d).triangle_angle_sum
    simp_rw [each]
    simp
  have edges : (T.graph.edgeFinset.card : ℝ) + 1 = Fintype.card T.vertices := by
    exact_mod_cast T.tree.card_edgeFinset
  have darts : (Fintype.card T.graph.Dart : ℝ) = 2 * T.graph.edgeFinset.card := by
    exact_mod_cast T.graph.dart_card_eq_twice_card_edges
  rw [corners]
  rw [reversed, darts] at triangles
  rw [← edges]
  linarith

end SixVertexUnfolding.ConvexPolyhedron.CutLocusTree
