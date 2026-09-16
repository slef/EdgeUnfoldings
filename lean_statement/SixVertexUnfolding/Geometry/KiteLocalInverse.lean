import SixVertexUnfolding.Geometry.KiteFolding
import SixVertexUnfolding.Geometry.StarDenseInterior
import SixVertexUnfolding.Geometry.StarDevelopmentContinuity
import SixVertexUnfolding.Geometry.DenseLocalInverse

/-! A planar neighborhood inside a kite has a true inverse surface
map. Dense interior uniqueness rules out an additional surface preimage
on the boundary between radial pieces. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

theorem develop_kite_fold {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (fold : (charts.global edge).Folding)
    (x : (charts.global edge).kite) (outside : fold.map x ∉ P.starCuts a) :
    charts.develop (fold.map x) = x.val :=
  graph.develop_agrees small_faces charts cofacial edge outside (fold.places x)

/-- An open region of a kite which folds into the uncut surface is an actual inverse chart. -/
theorem kite_fold_left_inverse {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (fold : (charts.global edge).Folding)
    (region : Set Plane) (open_region : IsOpen region) (contained : region ⊆ (charts.global edge).kite)
    (uncut : ∀ x : region, fold.map ⟨x, contained x.property⟩ ∉ P.starCuts a) :
    ∀ (b : P.UncutSurface a) (inside : charts.develop b.val ∈ region),
      fold.map ⟨charts.develop b.val, contained inside⟩ = b.val := by
  let development : C(P.UncutSurface a, Plane) :=
    ⟨fun b => charts.develop b.val, graph.develop_continuous small_faces charts cofacial⟩
  let inverse : C(region, P.UncutSurface a) :=
    ⟨fun x => ⟨fold.map ⟨x, contained x.property⟩, uncut x⟩,
      (fold.map.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  have right_inverse (x : region) : development (inverse x) = x.val :=
    graph.develop_kite_fold small_faces charts cofacial edge fold ⟨x, contained x.property⟩ (uncut x)
  have left_inverse := local_inverse_of_dense_unique development charts.triangleInteriorPoints
    (graph.triangle_interior_points_dense small_faces charts)
    (graph.develop_unique_on_dense_interiors small_faces charts source at_source cofacial)
    region open_region inverse right_inverse
  intro b inside
  exact congrArg Subtype.val (left_inverse b inside)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
