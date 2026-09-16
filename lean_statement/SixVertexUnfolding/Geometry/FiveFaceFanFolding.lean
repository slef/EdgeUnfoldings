import SixVertexUnfolding.Geometry.FiveFaceFanDevelopment
import SixVertexUnfolding.Geometry.FacetPlaneInverse
import SixVertexUnfolding.Geometry.FiniteSurfaceFolding

/-! The five opened triangles fold consistently onto their original faces,
including every shared radial edge and the common vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan.Development

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} {fan : P.FiveFaceFan pole}
  {slit : Fin 5} (net : fan.Development slit)

theorem inverse_formulas_joined (lift : Fin 5 → Plane →ᵃ[ℝ] Space)
    (inverse : ∀ i x, x ∈ (fan.face (slit + i)).val → lift i (net.place i x) = x) :
    ∀ i j x, x ∈ fan.openingTriangle slit i → x ∈ fan.openingTriangle slit j →
      lift i x = lift j x := by
  have at_pole (i : Fin 5) : lift i 0 = pole := by
    rw [← net.at_pole i]
    exact inverse i _ (fan.pole_mem_face _)
  have at_left (i : Fin 5) : lift i (fan.openingPoint slit i.castSucc) =
      fan.neighbor (slit + i) := by
    rw [← net.at_left i]
    exact inverse i _ (fan.left_mem_face _)
  have at_right (i : Fin 5) : lift i (fan.openingPoint slit i.succ) =
      fan.neighbor ((slit + i) + 1) := by
    rw [← net.at_right i]
    exact inverse i _ (fan.right_mem_face _)
  have adjacent (i : Fin 4) (x : Plane)
      (left : x ∈ fan.openingTriangle slit i.castSucc)
      (right : x ∈ fan.openingTriangle slit i.succ) : lift i.castSucc x = lift i.succ x := by
    have on_hinge : x ∈ segment ℝ 0 (fan.openingPoint slit i.castSucc.succ) := by
      rw [← fan.openingTriangles_adjacent_intersection slit i]
      exact ⟨left, right⟩
    have indices : (i.castSucc : Fin 5) + 1 = i.succ := by fin_cases i <;> decide
    have endpoint : lift i.castSucc (fan.openingPoint slit i.castSucc.succ) =
        lift i.succ (fan.openingPoint slit i.castSucc.succ) := by
      rw [at_right]
      change _ = lift i.succ (fan.openingPoint slit i.succ.castSucc)
      rw [at_left, add_assoc, indices]
    have agrees : EqOn (lift i.castSucc) (lift i.succ)
        ({0, fan.openingPoint slit i.castSucc.succ} : Set Plane) := by
      rintro x (rfl | rfl)
      · rw [at_pole, at_pole]
      · exact endpoint
    apply AffineMap.eqOn_affineSpan agrees
    rw [← convexHull_pair] at on_hinge
    exact convexHull_subset_affineSpan _ on_hinge
  have ordered (i j : Fin 5) (before : i < j) (x : Plane)
      (left : x ∈ fan.openingTriangle slit i)
      (right : x ∈ fan.openingTriangle slit j) : lift i x = lift j x := by
    by_cases gap : i.val + 1 < j.val
    · rw [fan.openingTriangles_meet_only_at_zero slit i j gap x left right, at_pole, at_pole]
    · let k : Fin 4 := ⟨i.val, by omega⟩
      have first : i = k.castSucc := Fin.ext rfl
      have second : j = k.succ := Fin.ext (by dsimp [k]; omega)
      rw [first, second]
      exact adjacent k x (by rwa [← first]) (by rwa [← second])
  intro i j x left right
  rcases lt_trichotomy i j with before | same | after
  · exact ordered i j before x left right
  · rw [same]
  · exact (ordered j i after x right left).symm

/-- An actual surface folding, with the original face maps as its right inverses. -/
theorem exists_surface_folding :
    ∃ fold : P.FiniteSurfaceFolding (Fin 5),
      (∀ i, fold.piece i = fan.openingTriangle slit i) ∧
      (∀ i x, x ∈ fan.triangle (slit + i) → fold.map (net.place i x) = x) := by
  classical
  choose lift in_plane right_inverse left_inverse rigid using fun i =>
    (fan.face (slit + i)).exists_rigid_plane_inverse (net.place i) (net.rigid i)
  have inverse (i : Fin 5) (x : Space) (hx : x ∈ (fan.face (slit + i)).val) :
      lift i (net.place i x) = x := left_inverse i x (subset_affineSpan ℝ _ hx)
  have on_surface (i : Fin 5) (x : Plane) (hx : x ∈ fan.openingTriangle slit i) :
      lift i x ∈ frontier P.body := by
    rw [← net.placed_triangle i] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [fan.triangle_eq_face] at hy
    rw [inverse i y hy]
    exact (fan.face _).subset_frontier hy
  let fold : P.FiniteSurfaceFolding (Fin 5) := {
    piece := fan.openingTriangle slit
    closed := fun i => ((Set.toFinite ({0, fan.openingPoint slit i.castSucc,
      fan.openingPoint slit i.succ} : Set Plane)).isCompact_convexHull ℝ).isClosed
    convex := fun _ => convex_convexHull ℝ _
    place := lift
    rigid := rigid
    on_surface := on_surface
    joined := net.inverse_formulas_joined lift inverse }
  refine ⟨fold, fun _ => rfl, ?_⟩
  intro i x hx
  have member : net.place i x ∈ fold.piece i := by
    change net.place i x ∈ fan.openingTriangle slit i
    rw [← net.placed_triangle i]
    exact ⟨x, hx, rfl⟩
  rw [fold.map_on_piece i member]
  exact inverse i x (by rwa [← fan.triangle_eq_face])

end SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan.Development
