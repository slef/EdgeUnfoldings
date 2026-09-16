import SixVertexUnfolding.Geometry.JunctionRayFolding
import SixVertexUnfolding.Geometry.SmallPolyhedronShortestRoutes

/-! Every retained junction ray has a continuous finite folding on
a neighborhood across its full open length, in any fixed global frame.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

theorem small_exists_source_ray_folding (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (p : fan.order.chart.sources) (route : P.BoundaryCurve)
    (member : route ∈ P.geodesicFiber a (T.vertexTarget u))
    (represented : fan.order.chart.Represents p route) (frame : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃ region : Set Plane, ∃ fold : C(region, frontier P.body),
      HasFiniteRigidPieces region (fun x => (fold x : Space)) ∧
      openSegment ℝ (frame p) (frame fan.order.chart.origin) ⊆ interior region ∧
      (∀ x : region, ∃ m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last,
        (fan.triangles m).placed.Places (fold x) (frame.symm x)) ∧
      (∀ (t : unitInterval) (inside : AffineMap.lineMap (frame p) (frame fan.order.chart.origin) (t : ℝ) ∈ region),
        fold ⟨_, inside⟩ = route t) := by
  obtain ⟨m, n, side, other, first_source, second_source, below, above⟩ := fan.exists_source_sides p
  let D := fan.triangles m
  let E := fan.triangles n
  let G := D.placed.inFrame frame
  let K := E.placed.inFrame frame
  let H := G.sideTriangle side
  let J := K.sideTriangle other
  have finite_routes := small_geodesicFiber_finite size small_faces a (T.vertexTarget u) (T.vertexTarget_different u)
  have first_route : D.routes side 0 = route := by
    have label := D.route_label side
    rw [first_source] at label
    exact fan.order.chart.represented_routes_agree finite_routes
      (by simpa only [T.closedEdgeTarget_zero] using D.routes_member side 0) member label represented
  have second_route : E.routes other 0 = route := by
    have label := E.route_label other
    rw [second_source] at label
    exact fan.order.chart.represented_routes_agree finite_routes
      (by simpa only [T.closedEdgeTarget_zero] using E.routes_member other 0) member label represented
  have G_source : G.motion (G.apex side) = frame p := congrArg frame first_source
  have K_source : K.motion (K.apex other) = frame p := congrArg frame second_source
  have G_root : G.motion G.model.left = frame fan.order.chart.origin := congrArg frame D.at_junction
  have K_root : K.motion K.model.left = frame fan.order.chart.origin := congrArg frame E.at_junction
  have opposite : det (G.motion (G.apex side) - G.motion G.model.left) (G.motion G.model.right - G.motion G.model.left) *
      det (K.motion (K.apex other) - K.motion K.model.left) (K.motion K.model.right - K.motion K.model.left) < 0 := by
    change det (frame (D.motion (D.apex side)) - frame (D.motion D.model.left))
        (frame (D.motion D.model.right) - frame (D.motion D.model.left)) *
      det (frame (E.motion (E.apex other)) - frame (E.motion E.model.left))
        (frame (E.motion E.model.right) - frame (E.motion E.model.left)) < 0
    rw [affine_det_product, D.at_junction, E.at_junction, first_source, second_source]
    exact mul_neg_of_neg_of_pos below above
  obtain ⟨fold, on_left, on_right, pieces⟩ := H.glue_left_ray J (first_route.trans second_route.symm)
    (G_source.trans K_source.symm) (G_root.trans K_root.symm) opposite
  let region := G.sideRegion side ∪ K.sideRegion other
  have interior_ray : openSegment ℝ (frame p) (frame fan.order.chart.origin) ⊆ interior region := by
    have domain_eq : region =
        convexHull ℝ ({frame p, frame fan.order.chart.origin, G.motion G.model.right} : Set Plane) ∪
        convexHull ℝ ({frame p, frame fan.order.chart.origin, K.motion K.model.right} : Set Plane) := by
      change convexHull ℝ ({G.motion (G.apex side), G.motion G.model.left, G.motion G.model.right} : Set Plane) ∪
        convexHull ℝ ({K.motion (K.apex other), K.motion K.model.left, K.motion K.model.right} : Set Plane) = _
      rw [G_source, K_source, G_root, K_root]
    rw [domain_eq]
    have signed := opposite
    rw [G_source, K_source, G_root, K_root] at signed
    simpa only [insert_comm (frame p) (frame fan.order.chart.origin),
      openSegment_symm ℝ (frame p) (frame fan.order.chart.origin)] using
      open_base_in_joined_triangles_of_opposite (frame fan.order.chart.origin) (frame p)
        (G.motion G.model.right) (K.motion K.model.right) signed
  refine ⟨region, fold, pieces, interior_ray, ?_, ?_⟩
  · intro x
    rcases x.property with first | second
    · have placed : G.Places (fold x) x.val := by
        have at_x : fold x = (H.homeomorph.symm ⟨x, first⟩).val := on_left ⟨x, first⟩
        rw [at_x]
        exact ⟨side, (H.homeomorph.symm ⟨x, first⟩).property,
          congrArg Subtype.val (H.homeomorph.apply_symm_apply ⟨x, first⟩)⟩
      exact ⟨m, (D.placed.places_inFrame frame (fold x) x).mp placed⟩
    · have placed : K.Places (fold x) x.val := by
        have at_x : fold x = (J.homeomorph.symm ⟨x, second⟩).val := on_right ⟨x, second⟩
        rw [at_x]
        exact ⟨other, (J.homeomorph.symm ⟨x, second⟩).property,
          congrArg Subtype.val (J.homeomorph.apply_symm_apply ⟨x, second⟩)⟩
      exact ⟨n, (E.placed.places_inFrame frame (fold x) x).mp placed⟩
  · intro t inside
    let q := AffineMap.lineMap (G.motion (G.apex side)) (G.motion G.model.left) (t : ℝ)
    have q_in : q ∈ G.sideRegion side := by
      change AffineMap.lineMap (G.motion (G.apex side)) (G.motion G.model.left) (t : ℝ) ∈
        convexHull ℝ ({G.motion (G.apex side), G.motion G.model.left, G.motion G.model.right} : Set Plane)
      apply (convex_convexHull ℝ _).mapsTo_lineMap
      · exact subset_convexHull ℝ _ (Or.inl rfl)
      · exact subset_convexHull ℝ _ (Or.inr (Or.inl rfl))
      · exact t.property
    have position : q = AffineMap.lineMap (frame p) (frame fan.order.chart.origin) (t : ℝ) := by
      dsimp [q]
      rw [G_source, G_root]
    calc
      fold ⟨_, inside⟩ = fold ⟨q, Or.inl q_in⟩ := congrArg fold (Subtype.ext position.symm)
      _ = (H.homeomorph.symm ⟨q, q_in⟩).val := on_left ⟨q, q_in⟩
      _ = D.routes side 0 t := H.fold_on_left_ray t q_in
      _ = route t := congrArg (fun f : P.BoundaryCurve => f t) first_route

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
