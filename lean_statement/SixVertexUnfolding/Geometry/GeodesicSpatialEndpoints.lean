import SixVertexUnfolding.Geometry.GeodesicFibers

/-! Ambient endpoint coordinates let a geodesic family be compared with
an affine line even when that line is extended outside the surface. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

/-- The two actual spatial endpoints of a normalized boundary curve. -/
noncomputable def spatialEndpoints (P : ConvexPolyhedron) : C(P.BoundaryCurve, Space × Space) :=
  ⟨fun f => ((f 0 : Space), (f 1 : Space)),
    (continuous_subtype_val.comp (continuous_eval_const 0)).prodMk
      (continuous_subtype_val.comp (continuous_eval_const 1))⟩

/-- Spatial endpoint equality and intrinsic endpoint equality describe the same fiber. -/
theorem spatial_geodesic_fiber (P : ConvexPolyhedron) (a b : frontier P.body) :
    P.geodesicCurves ∩ P.spatialEndpoints ⁻¹' {((a : Space), (b : Space))} =
      P.geodesicFiber a b := by
  ext f
  constructor
  · rintro ⟨geodesic, endpoints⟩
    exact ⟨geodesic, Prod.ext (Subtype.ext (congrArg Prod.fst endpoints))
      (Subtype.ext (congrArg Prod.snd endpoints))⟩
  · rintro ⟨geodesic, endpoints⟩
    exact ⟨geodesic, Prod.ext (congrArg Subtype.val (congrArg Prod.fst endpoints))
      (congrArg Subtype.val (congrArg Prod.snd endpoints))⟩

end SixVertexUnfolding.ConvexPolyhedron
