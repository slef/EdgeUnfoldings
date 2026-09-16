import SixVertexUnfolding.Geometry.GeodesicCurveCompactness

/-! The compact family's metric geodesics are precisely genuine normalized
shortest surface paths. The comparison still allows every continuous competitor. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set
open scoped ENNReal NNReal

/-- Turn a boundary-valued curve into an actual surface path with its own endpoints. -/
noncomputable def surfacePathOfCurve (P : ConvexPolyhedron) (f : P.BoundaryCurve) :
    P.SurfacePath (f 0) (f 1) where
  curve := {
    toFun := fun t => (f t : Space)
    continuous_toFun := continuous_subtype_val.comp f.continuous
    source' := rfl
    target' := rfl }
  on_surface t := (f t).property

/-- The intrinsic geodesic equation gives the exact optimal length and its constant speed. -/
theorem surfacePathOfCurve_shortest (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) :
    (P.surfacePathOfCurve f).IsShortest ∧ (P.surfacePathOfCurve f).length ≠ ⊤ ∧
      LipschitzWith (P.surfacePathOfCurve f).length.toNNReal (P.surfacePathOfCurve f).curve := by
  let path := P.surfacePathOfCurve f
  let distance := P.surfaceEDist (f 0) (f 1)
  have finite : distance ≠ ⊤ := P.surfaceEDist_ne_top (f 0).property (f 1).property
  have speed : LipschitzWith distance.toNNReal path.curve := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have lower := P.dist_le_surfaceDist (f s).property (f t).property
    rw [geodesic s t] at lower
    simpa only [ENNReal.coe_toNNReal_eq_toReal] using lower
  have upper : path.length ≤ distance :=
    (path.length_le_of_lipschitz speed).trans_eq (ENNReal.coe_toNNReal finite)
  have equal : path.length = distance := le_antisymm upper path.surfaceEDist_le_length
  refine ⟨?_, equal ▸ finite, ?_⟩
  · intro other
    exact equal ▸ other.surfaceEDist_le_length
  · rwa [equal]

/-- Converting a boundary curve to a path and back preserves the entire curve. -/
theorem surfacePathOfCurve_boundaryCurve (P : ConvexPolyhedron) (f : P.BoundaryCurve) :
    (P.surfacePathOfCurve f).boundaryCurve = f := by
  apply BoundedContinuousFunction.ext
  intro t
  rfl

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b a' b' : Space}

/-- Change only the names of endpoints identified by equalities. -/
noncomputable def cast (path : P.SurfacePath a b) (ha : a' = a) (hb : b' = b) : P.SurfacePath a' b' where
  curve := path.curve.cast ha hb
  on_surface := path.on_surface

theorem cast_length (path : P.SurfacePath a b) (ha : a' = a) (hb : b' = b) :
    (path.cast ha hb).length = path.length := rfl

theorem cast_shortest (path : P.SurfacePath a b) (ha : a' = a) (hb : b' = b) (shortest : path.IsShortest) :
    (path.cast ha hb).IsShortest := by
  cases ha
  cases hb
  exact shortest

theorem cast_boundaryCurve (path : P.SurfacePath a b) (ha : a' = a) (hb : b' = b) :
    (path.cast ha hb).boundaryCurve = path.boundaryCurve := rfl

end SurfacePath
end SixVertexUnfolding.ConvexPolyhedron
