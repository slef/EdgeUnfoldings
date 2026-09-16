import SixVertexUnfolding.Geometry.StarPatchDistance
import SixVertexUnfolding.Geometry.FiniteFoldingMetric

/-! A proved local inverse folding gives the reverse distance bound.
Together with the assembled forward bound, a convex flat patch is rigid. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

theorem develop_flat_patch_isometric_of_folding {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {z : Space} (flat : P.FlatChart z) (patch : Set Plane) (convex_patch : Convex ℝ patch)
    (in_domain : patch ⊆ flat.domain) (inclusion : C(patch, P.UncutSurface a))
    (located : ∀ x, ((inclusion x).val : Space) = flat.map (x : Plane))
    (region : Set Plane) (fold : C(region, frontier P.body))
    (pieces : HasFiniteRigidPieces region (fun x => (fold x : Space)))
    (inside : ∀ x : patch, charts.develop (inclusion x).val ∈ region)
    (recovers : ∀ x : patch, fold ⟨charts.develop (inclusion x).val, inside x⟩ = (inclusion x).val)
    (segments : ∀ x y : patch,
      segment ℝ (charts.develop (inclusion x).val) (charts.develop (inclusion y).val) ⊆ region) :
    Isometry (fun x => charts.develop (inclusion x).val) := by
  have forward := graph.develop_flat_patch_nonexpanding small_faces charts cofacial flat patch
    convex_patch in_domain inclusion located
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa only [NNReal.coe_one, one_mul] using forward.dist_le_mul x y
  · have backward := finite_folding_segment_distance fold pieces
      ⟨charts.develop (inclusion x).val, inside x⟩ ⟨charts.develop (inclusion y).val, inside y⟩ (segments x y)
    rw [recovers x, recovers y, located x, located y,
      flat.distance x (in_domain x.property) y (in_domain y.property)] at backward
    exact backward

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
