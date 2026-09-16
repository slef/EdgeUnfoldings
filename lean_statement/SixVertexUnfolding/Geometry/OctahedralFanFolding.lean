import SixVertexUnfolding.Geometry.OctahedralFanIntersections
import SixVertexUnfolding.Geometry.FacetPlaneInverse
import SixVertexUnfolding.Geometry.FiniteSurfaceFolding

/-! The explicit opened four-triangle fan folds back onto the actual
polyhedron, including its shared edges and its pole. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.FanDevelopment

open Set OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
  {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4}
  {pole : Fin 6} {slit : Fin 4} (fan : graph.FanDevelopment small_faces pole slit)

/-- The four spatial inverses agree on every contact of the developed triangles. -/
theorem inverse_formulas_joined (lift : Fin 4 → Plane →ᵃ[ℝ] Space)
    (inverse : ∀ i x, x ∈ (graph.triangleFace small_faces (fanTriangle pole (slit + i))).val →
      lift i (fan.place i x) = x) :
    ∀ i j x, x ∈ graph.openingTriangle pole slit i → x ∈ graph.openingTriangle pole slit j →
      lift i x = lift j x := by
  have at_pole (i : Fin 4) : lift i 0 = graph.vertex pole := by
    rw [← fan.at_pole i]
    exact inverse i _ (graph.fan_sector_on_face pole small_faces (slit + i) _ (by simp))
  have at_left (i : Fin 4) : lift i (graph.openingPoint pole slit i.castSucc) =
      graph.vertex (fanNeighbor pole (slit + i)) := by
    rw [← fan.at_left i]
    exact inverse i _ (graph.fan_sector_on_face pole small_faces (slit + i) _ (by simp))
  have at_right (i : Fin 4) : lift i (graph.openingPoint pole slit i.succ) =
      graph.vertex (fanNeighbor pole ((slit + i) + 1)) := by
    rw [← fan.at_right i]
    exact inverse i _ (graph.fan_sector_on_face pole small_faces (slit + i) _ (by simp))
  have adjacent (i : Fin 3) (x : Plane)
      (left : x ∈ graph.openingTriangle pole slit i.castSucc)
      (right : x ∈ graph.openingTriangle pole slit i.succ) : lift i.castSucc x = lift i.succ x := by
    have on_hinge : x ∈ segment ℝ 0 (graph.openingPoint pole slit i.castSucc.succ) := by
      rw [← graph.openingTriangles_adjacent_intersection pole slit i]
      exact ⟨left, right⟩
    have indices : (i.castSucc : Fin 4) + 1 = i.succ := by fin_cases i <;> decide
    have endpoint : lift i.castSucc (graph.openingPoint pole slit i.castSucc.succ) =
        lift i.succ (graph.openingPoint pole slit i.castSucc.succ) := by
      rw [at_right]
      change _ = lift i.succ (graph.openingPoint pole slit i.succ.castSucc)
      rw [at_left, add_assoc, indices]
    have agrees : EqOn (lift i.castSucc) (lift i.succ)
        ({0, graph.openingPoint pole slit i.castSucc.succ} : Set Plane) := by
      rintro x (rfl | rfl)
      · rw [at_pole, at_pole]
      · exact endpoint
    apply AffineMap.eqOn_affineSpan agrees
    rw [← convexHull_pair] at on_hinge
    exact convexHull_subset_affineSpan _ on_hinge
  have ordered (i j : Fin 4) (before : i < j) (x : Plane)
      (left : x ∈ graph.openingTriangle pole slit i)
      (right : x ∈ graph.openingTriangle pole slit j) : lift i x = lift j x := by
    by_cases gap : i.val + 1 < j.val
    · rw [graph.openingTriangles_meet_only_at_zero small_faces pole slit i j gap x left right,
        at_pole, at_pole]
    · let k : Fin 3 := ⟨i.val, by omega⟩
      have first : i = k.castSucc := Fin.ext rfl
      have second : j = k.succ := Fin.ext (by dsimp [k]; omega)
      rw [first, second]
      exact adjacent k x (by rwa [← first]) (by rwa [← second])
  intro i j x left right
  rcases lt_trichotomy i j with before | same | after
  · exact ordered i j before x left right
  · rw [same]
  · exact (ordered j i after x right left).symm

/-- The developed fan has a genuine rigid folding back to its original surface triangles. -/
theorem exists_surface_folding :
    ∃ fold : P.FiniteSurfaceFolding (Fin 4),
      (∀ i, fold.piece i = graph.openingTriangle pole slit i) ∧
      (∀ i x, x ∈ graph.triangle (fanTriangle pole (slit + i)) →
        fold.map (fan.place i x) = x) := by
  classical
  choose lift in_plane right_inverse left_inverse rigid using fun i =>
    (graph.triangleFace small_faces (fanTriangle pole (slit + i))).exists_rigid_plane_inverse
      (fan.place i) (fan.rigid i)
  have inverse (i : Fin 4) (x : Space)
      (hx : x ∈ (graph.triangleFace small_faces (fanTriangle pole (slit + i))).val) :
      lift i (fan.place i x) = x := left_inverse i x (subset_affineSpan ℝ _ hx)
  have on_surface (i : Fin 4) (x : Plane) (hx : x ∈ graph.openingTriangle pole slit i) :
      lift i x ∈ frontier P.body := by
    rw [← fan.placed_triangle i] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have in_face := graph.triangle_subset_face small_faces _ hy
    rw [inverse i y in_face]
    exact (graph.triangleFace small_faces _).subset_frontier in_face
  let fold : P.FiniteSurfaceFolding (Fin 4) := {
    piece := graph.openingTriangle pole slit
    closed := fun i => ((Set.toFinite ({0, graph.openingPoint pole slit i.castSucc,
      graph.openingPoint pole slit i.succ} : Set Plane)).isCompact_convexHull ℝ).isClosed
    convex := fun _ => convex_convexHull ℝ _
    place := lift
    rigid := rigid
    on_surface := on_surface
    joined := fan.inverse_formulas_joined lift inverse }
  refine ⟨fold, fun _ => rfl, ?_⟩
  intro i x hx
  have member : fan.place i x ∈ fold.piece i := by
    change fan.place i x ∈ graph.openingTriangle pole slit i
    rw [← fan.placed_triangle i]
    exact ⟨x, hx, rfl⟩
  rw [fold.map_on_piece i member]
  exact inverse i x (graph.triangle_subset_face small_faces _ hx)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.FanDevelopment
