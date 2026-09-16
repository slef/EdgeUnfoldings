import SixVertexUnfolding.Geometry.TerminalSourceRecovery
import SixVertexUnfolding.Geometry.MultipleRouteTopology

/-! Every source, including an original vertex, has a neighborhood with
unique straight shortest routes. Multiple-route targets cannot accumulate there. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Any two points of one whole face have a unique normalized shortest route on the entire surface. -/
theorem geodesicFiber_cofacial_unique (P : ConvexPolyhedron) (a b : frontier P.body)
    (F : P.Face) (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) :
    (P.geodesicFiber a b).Subsingleton := by
  intro f hf g hg
  obtain ⟨first, hs, fs, cs, first_eq⟩ := P.geodesicFiber_path a b f hf
  obtain ⟨second, ht, ft, ct, second_eq⟩ := P.geodesicFiber_path a b g hg
  have coordinates (path : P.SurfacePath a b) (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
      (speed : LipschitzWith path.length.toNNReal path.curve) (t : unitInterval) :
      P.faceCoordinates F (path.curve t) = AffineMap.lineMap (P.faceCoordinates F a) (P.faceCoordinates F b) (t : ℝ) := by
    have formula := path.face_coordinates_eq_lineMap shortest finite speed F 0 1 (by norm_num)
      (by simpa only [path.curve.source] using aF) (by simpa only [path.curve.target] using bF) t t.property
    simpa only [path.curve.source, path.curve.target,
      show ((0 : unitInterval) : ℝ) = 0 from rfl, show ((1 : unitInterval) : ℝ) = 1 from rfl,
      sub_zero, div_one] using formula
  have agree (t : unitInterval) : first.curve t = second.curve t := by
    have firstF := F.convex.segment_subset aF bF (first.shortest_cofacial_range_subset hs F aF bF ⟨t, rfl⟩)
    have secondF := F.convex.segment_subset aF bF (second.shortest_cofacial_range_subset ht F aF bF ⟨t, rfl⟩)
    apply dist_eq_zero.mp
    rw [← P.faceCoordinates_rigid F _ firstF _ secondF, coordinates first hs fs cs t,
      coordinates second ht ft ct t, dist_self]
  rw [← first_eq, ← second_eq, first.eq_of_curve_eq second agree]

/-- All sufficiently near boundary targets have a unique route from the source, for every public polyhedron. -/
theorem unique_routes_near_source (P : ConvexPolyhedron) (a : frontier P.body) :
    ∃ U : Set Space, IsOpen U ∧ (a : Space) ∈ U ∧
      ∀ b : frontier P.body, (b : Space) ∈ U → (P.geodesicFiber a b).Subsingleton := by
  obtain ⟨U, openU, aU, incident⟩ := P.incident_facets_neighborhood a
  refine ⟨U, openU, aU, ?_⟩
  intro b bU
  obtain ⟨F, bF⟩ := P.boundary_point_in_face b.property
  exact P.geodesicFiber_cofacial_unique a b F (incident b bU F bF) bF

/-- The closure of the actual multiple-route locus never contains its source. -/
theorem source_not_closure_multiple_routes (P : ConvexPolyhedron) (a : frontier P.body) :
    a ∉ closure {b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} := by
  obtain ⟨U, openU, aU, unique⟩ := P.unique_routes_near_source a
  intro limit
  obtain ⟨b, bU, multiple⟩ := mem_closure_iff.mp limit (Subtype.val ⁻¹' U)
    (openU.preimage continuous_subtype_val) aU
  exact ((P.multiple_routes_iff_fiber a b).mp multiple).2 (unique b bU)

end SixVertexUnfolding.ConvexPolyhedron
