import SixVertexUnfolding.Geometry.ShortestFaceSubdivision
import SixVertexUnfolding.Geometry.GeodesicCurvePaths

/-! Every shortest route is covered by one straight chord for each
original facet. This finite cover is enough for the surface-density
argument; no generic dimension or measure theory is needed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b : Space} (path : P.SurfacePath a b)

/-- Every point of a shortest route lies on the entry-to-exit chord of a visited face. -/
theorem shortest_in_face_chord (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (t : unitInterval) : ∃ F : P.Face,
      path.curve t ∈ segment ℝ (path.curve (path.faceEntry F)) (path.curve (path.faceExit F)) := by
  obtain ⟨F, on_face⟩ := P.boundary_point_in_face (path.on_surface t)
  have visits : ∃ s, path.curve s ∈ F.val := ⟨t, on_face⟩
  have first := (path.face_visits_compact F).sInf_mem visits
  have last := (path.face_visits_compact F).sSup_mem visits
  have between : t ∈ Icc (path.faceEntry F) (path.faceExit F) :=
    (path.shortest_face_visits_eq_interval shortest finite F visits) ▸ on_face
  exact ⟨F, path.shortest_portion_range shortest finite F _ _ (between.1.trans between.2)
    first last t between⟩

end SurfacePath

/-- A finite explicit chord family covers the whole normalized geodesic. -/
theorem geodesic_range_segment_cover (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) :
    ∃ p q : P.Face → Space, ∀ t, ∃ F, (f t : Space) ∈ segment ℝ (p F) (q F) := by
  let path := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, _⟩ := P.surfacePathOfCurve_shortest f geodesic
  exact ⟨fun F => path.curve (path.faceEntry F), fun F => path.curve (path.faceExit F),
    path.shortest_in_face_chord shortest finite⟩

end SixVertexUnfolding.ConvexPolyhedron
