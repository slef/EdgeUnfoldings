import SixVertexUnfolding.Geometry.KiteLocalInverse
import SixVertexUnfolding.Geometry.SmallPolyhedronStarDenseInterior
import SixVertexUnfolding.Geometry.SmallPolyhedronStarDevelopmentContinuity

/-! A planar neighborhood inside a kite has a true inverse surface
map. Dense interior uniqueness rules out an additional surface preimage
on the boundary between radial pieces.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

theorem small_develop_kite_fold {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (fold : (charts.global edge).Folding)
    (x : (charts.global edge).kite) (outside : fold.map x ∉ P.starCuts a) :
    charts.develop (fold.map x) = x.val :=
  small_develop_agrees size small_faces charts cofacial edge outside (fold.places x)

/-- An open region of a kite which folds into the uncut surface is an actual inverse chart. -/
theorem small_kite_fold_left_inverse {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (fold : (charts.global edge).Folding)
    (region : Set Plane) (open_region : IsOpen region) (contained : region ⊆ (charts.global edge).kite)
    (uncut : ∀ x : region, fold.map ⟨x, contained x.property⟩ ∉ P.starCuts a) :
    ∀ (b : P.UncutSurface a) (inside : charts.develop b.val ∈ region),
      fold.map ⟨charts.develop b.val, contained inside⟩ = b.val := by
  let development : C(P.UncutSurface a, Plane) :=
    ⟨fun b => charts.develop b.val, small_develop_continuous size small_faces charts cofacial⟩
  let inverse : C(region, P.UncutSurface a) :=
    ⟨fun x => ⟨fold.map ⟨x, contained x.property⟩, uncut x⟩,
      (fold.map.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  have right_inverse (x : region) : development (inverse x) = x.val :=
    small_develop_kite_fold size small_faces charts cofacial edge fold ⟨x, contained x.property⟩ (uncut x)
  have left_inverse := local_inverse_of_dense_unique development charts.triangleInteriorPoints
    (small_triangle_interior_points_dense size small_faces charts)
    (small_develop_unique_on_dense_interiors size small_faces charts separated cofacial)
    region open_region inverse right_inverse
  intro b inside
  exact congrArg Subtype.val (left_inverse b inside)

end SixVertexUnfolding.ConvexPolyhedron
