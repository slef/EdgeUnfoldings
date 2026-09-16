import SixVertexUnfolding.Geometry.StarForwardPieces
import SixVertexUnfolding.Geometry.ConvexFiniteSelection

/-! The assembled map does not stretch convex patches, including
patches crossing radial triangle boundaries and original hinges. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- A convex uncut patch on the actual surface has a nonexpanding development. -/
theorem develop_convex_patch_nonexpanding {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (patch : Set Space) (convex_patch : Convex ℝ patch) (inclusion : C(patch, P.UncutSurface a))
    (located : ∀ x, ((inclusion x).val : Space) = (x : Space)) :
    LipschitzWith 1 (fun x => charts.develop (inclusion x).val) := by
  obtain ⟨maps, finite_maps, bounded, selected⟩ := charts.finite_forward_pieces
  letI : Finite maps := finite_maps.to_subtype
  apply convex_subtype_finite_selection_lipschitz patch convex_patch
    (fun x => charts.develop (inclusion x).val) (fun g : maps => g.val) 1
    ((graph.develop_continuous small_faces charts cofacial).comp inclusion.continuous)
    (fun g => (bounded g.val g.property).lipschitzOnWith)
  intro x
  obtain ⟨g, member, at_x⟩ := selected (inclusion x).val
  exact ⟨⟨g, member⟩, at_x.trans (congrArg g (located x))⟩

/-- The same bound holds in any actual flat chart, including across an original edge. -/
theorem develop_flat_patch_nonexpanding {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {z : Space} (flat : P.FlatChart z) (patch : Set Plane) (convex_patch : Convex ℝ patch)
    (in_domain : patch ⊆ flat.domain) (inclusion : C(patch, P.UncutSurface a))
    (located : ∀ x, ((inclusion x).val : Space) = flat.map (x : Plane)) :
    LipschitzWith 1 (fun x => charts.develop (inclusion x).val) := by
  obtain ⟨maps, finite_maps, bounded, selected⟩ := charts.finite_forward_pieces
  letI : Finite maps := finite_maps.to_subtype
  apply convex_subtype_finite_selection_lipschitz patch convex_patch
    (fun x => charts.develop (inclusion x).val) (fun g : maps => g.val ∘ flat.map) 1
    ((graph.develop_continuous small_faces charts cofacial).comp inclusion.continuous)
  · intro g
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have projection := (bounded g.val g.property).dist_le_mul (flat.map x) (flat.map y)
    have chord := P.dist_le_surfaceDist (flat.on_surface (in_domain hx)) (flat.on_surface (in_domain hy))
    rw [flat.distance x (in_domain hx) y (in_domain hy)] at chord
    have projection_bound : dist (g.val (flat.map x)) (g.val (flat.map y)) ≤ dist (flat.map x) (flat.map y) := by
      simpa only [NNReal.coe_one, one_mul] using projection
    simpa only [Function.comp_apply, NNReal.coe_one, one_mul] using projection_bound.trans chord
  · intro x
    obtain ⟨g, member, at_x⟩ := selected (inclusion x).val
    exact ⟨⟨g, member⟩, at_x.trans (congrArg g (located x))⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
