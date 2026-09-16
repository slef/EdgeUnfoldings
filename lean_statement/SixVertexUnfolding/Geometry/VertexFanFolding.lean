import SixVertexUnfolding.Geometry.VertexFanDevelopment
import SixVertexUnfolding.Geometry.FacetPlaneInverse
import SixVertexUnfolding.Geometry.FiniteSurfaceFolding

/-! The opened corner triangles fold consistently onto their original faces,
including every shared radial edge and the common vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan.Development

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  {fan : P.VertexFaceFan pole n}
  {slit : Fin n} (net : fan.Development slit)

theorem inverse_formulas_joined (deficit : fan.totalAngle < 2 * Real.pi) (lift : Fin n → Plane →ᵃ[ℝ] Space)
    (inverse : ∀ i x, x ∈ (fan.face (slit + i)).val → lift i (net.place i x) = x) :
    ∀ i j x, x ∈ fan.openingTriangle slit i → x ∈ fan.openingTriangle slit j →
      lift i x = lift j x := by
  have at_pole (i : Fin n) : lift i 0 = pole := by
    rw [← net.at_pole i]
    exact inverse i _ (fan.pole_mem _)
  have at_left (i : Fin n) : lift i (fan.openingPoint slit i.castSucc) =
      fan.neighbor (slit + i) := by
    rw [← net.at_left i]
    exact inverse i _ (fan.left_mem _)
  have at_right (i : Fin n) : lift i (fan.openingPoint slit i.succ) =
      fan.neighbor ((slit + i) + 1) := by
    rw [← net.at_right i]
    exact inverse i _ (fan.right_mem _)
  have adjacent (i j : Fin n) (next : j.val = i.val + 1) (x : Plane)
      (left : x ∈ fan.openingTriangle slit i)
      (right : x ∈ fan.openingTriangle slit j) : lift i x = lift j x := by
    have on_hinge : x ∈ segment ℝ 0 (fan.openingPoint slit i.succ) := by
      rw [← fan.openingTriangles_adjacent_intersection slit i j next]
      exact ⟨left, right⟩
    have seam : i.succ = j.castSucc := Fin.ext next.symm
    have indices : i + 1 = j := by
      apply Fin.ext
      change (i.val + 1 % n) % n = j.val
      calc
        _ = (i.val + 1) % n := by
          simpa only [Nat.mod_eq_of_lt i.isLt] using (Nat.add_mod i.val 1 n).symm
        _ = j.val := by
          rw [Nat.mod_eq_of_lt (show i.val + 1 < n by omega)]
          exact next.symm
    have endpoint : lift i (fan.openingPoint slit i.succ) = lift j (fan.openingPoint slit i.succ) := by
      rw [at_right, seam, at_left, add_assoc, indices]
    have agrees : EqOn (lift i) (lift j) ({0, fan.openingPoint slit i.succ} : Set Plane) := by
      rintro y (rfl | rfl)
      · rw [at_pole, at_pole]
      · exact endpoint
    apply AffineMap.eqOn_affineSpan agrees
    rw [← convexHull_pair] at on_hinge
    exact convexHull_subset_affineSpan _ on_hinge
  have ordered (i j : Fin n) (before : i < j) (x : Plane)
      (left : x ∈ fan.openingTriangle slit i)
      (right : x ∈ fan.openingTriangle slit j) : lift i x = lift j x := by
    by_cases gap : i.val + 1 < j.val
    · rw [fan.openingTriangles_meet_only_at_zero slit i j deficit gap x left right, at_pole, at_pole]
    · exact adjacent i j (by omega) x left right
  intro i j x left right
  rcases lt_trichotomy i j with before | same | after
  · exact ordered i j before x left right
  · rw [same]
  · exact (ordered j i after x right left).symm

/-- An actual surface folding, with the original face maps as its right inverses. -/
theorem exists_surface_folding (deficit : fan.totalAngle < 2 * Real.pi) :
    ∃ fold : P.FiniteSurfaceFolding (Fin n),
      (∀ i, fold.piece i = fan.openingTriangle slit i) ∧
      (∀ i x, x ∈ fan.triangle (slit + i) → fold.map (net.place i x) = x) := by
  classical
  choose lift in_plane right_inverse left_inverse rigid using fun i =>
    (fan.face (slit + i)).exists_rigid_plane_inverse (net.place i) (net.rigid i)
  have inverse (i : Fin n) (x : Space) (hx : x ∈ (fan.face (slit + i)).val) :
      lift i (net.place i x) = x := left_inverse i x (subset_affineSpan ℝ _ hx)
  have on_surface (i : Fin n) (x : Plane) (hx : x ∈ fan.openingTriangle slit i) :
      lift i x ∈ frontier P.body := by
    rw [← net.placed_triangle i] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have on_face := fan.triangle_subset_face _ hy
    rw [inverse i y on_face]
    exact (fan.face _).subset_frontier on_face
  let fold : P.FiniteSurfaceFolding (Fin n) := {
    piece := fan.openingTriangle slit
    closed := fun i => ((Set.toFinite ({0, fan.openingPoint slit i.castSucc,
      fan.openingPoint slit i.succ} : Set Plane)).isCompact_convexHull ℝ).isClosed
    convex := fun _ => convex_convexHull ℝ _
    place := lift
    rigid := rigid
    on_surface := on_surface
    joined := net.inverse_formulas_joined deficit lift inverse }
  refine ⟨fold, fun _ => rfl, ?_⟩
  intro i x hx
  have member : net.place i x ∈ fold.piece i := by
    change net.place i x ∈ fan.openingTriangle slit i
    rw [← net.placed_triangle i]
    exact ⟨x, hx, rfl⟩
  rw [fold.map_on_piece i member]
  exact inverse i x (fan.triangle_subset_face _ hx)

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan.Development
