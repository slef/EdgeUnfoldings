import SixVertexUnfolding.Geometry.UniqueGeodesicPrefixes
import Mathlib.Topology.Homotopy.Contractible

/-! The set of targets with a unique shortest route contracts to the source
along those routes. This holds for every public convex polyhedron. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A metric geodesic with equal endpoints is constant. -/
theorem geodesic_same_endpoints (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (same : f 0 = f 1) (t : unitInterval) : f t = f 0 := by
  have zero := geodesic 0 t
  rw [← same, P.surfaceDist_self (f 0).property, zero_mul] at zero
  exact Subtype.ext ((P.surfaceDist_eq_zero_iff (f 0).property (f t).property).mp zero).symm

theorem geodesicFiber_self (P : ConvexPolyhedron) (a : frontier P.body) :
    (P.geodesicFiber a a).Subsingleton := by
  intro f hf g hg
  have f0 : f 0 = a := congrArg Prod.fst hf.2
  have f1 : f 1 = a := congrArg Prod.snd hf.2
  have g0 : g 0 = a := congrArg Prod.fst hg.2
  have g1 : g 1 = a := congrArg Prod.snd hg.2
  apply BoundedContinuousFunction.ext
  intro t
  rw [P.geodesic_same_endpoints f hf.1 (f0.trans f1.symm),
    P.geodesic_same_endpoints g hg.1 (g0.trans g1.symm), f0, g0]

/-- Uniqueness passes to all initial targets, including the source itself. -/
theorem unique_geodesic_initial_targets (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (unique : (P.geodesicFiber (f 0) (f 1)).Subsingleton)
    (t : unitInterval) : (P.geodesicFiber (f 0) (f t)).Subsingleton := by
  by_cases same : f 0 = f 1
  · rw [P.geodesic_same_endpoints f geodesic same t]
    exact P.geodesicFiber_self (f 0)
  · exact P.unique_geodesic_prefixes f geodesic unique same t

/-- Boundary targets joined to the source by exactly one normalized shortest route. -/
def uniqueTargets (P : ConvexPolyhedron) (a : frontier P.body) : Set (frontier P.body) :=
  {b | (P.geodesicFiber a b).Subsingleton}

theorem chosenGeodesic_stays_unique (P : ConvexPolyhedron) (a b : frontier P.body)
    (unique : b ∈ P.uniqueTargets a) (t : unitInterval) :
    P.chosenGeodesic (a, b) t ∈ P.uniqueTargets a := by
  have member := P.chosenGeodesic_mem (a, b)
  have first : P.chosenGeodesic (a, b) 0 = a := congrArg Prod.fst member.2
  have last : P.chosenGeodesic (a, b) 1 = b := congrArg Prod.snd member.2
  have initial := P.unique_geodesic_initial_targets (P.chosenGeodesic (a, b)) member.1
    (by simpa only [first, last] using unique) t
  simpa only [first] using initial

/-- The entire unique-route target set is contractible through its unique shortest routes. -/
theorem uniqueTargets_contractible (P : ConvexPolyhedron) (a : frontier P.body) :
    ContractibleSpace (P.uniqueTargets a) := by
  let center : P.uniqueTargets a := ⟨a, P.geodesicFiber_self a⟩
  have selected : Continuous (fun b : P.uniqueTargets a => P.chosenGeodesic (a, b.val)) := by
    have endpoints : Continuous (fun b : P.uniqueTargets a => (a, b.val)) :=
      continuous_const.prodMk continuous_subtype_val
    apply continuous_iff_continuousAt.mpr
    intro b
    exact ContinuousAt.comp (f := fun c : P.uniqueTargets a => (a, c.val)) (x := b)
      (P.chosenGeodesic_continuousAt (a, b.val) b.property) endpoints.continuousAt
  let contraction : ContinuousMap.Homotopy (ContinuousMap.const (P.uniqueTargets a) center)
      (ContinuousMap.id (P.uniqueTargets a)) := {
    toFun := fun pair => ⟨P.chosenGeodesic (a, pair.2.val) pair.1,
      P.chosenGeodesic_stays_unique a pair.2.val pair.2.property pair.1⟩
    continuous_toFun := (continuous_eval.comp ((selected.comp continuous_snd).prodMk continuous_fst)).subtype_mk _
    map_zero_left := fun b => Subtype.ext (congrArg Prod.fst (P.chosenGeodesic_mem (a, b.val)).2)
    map_one_left := fun b => Subtype.ext (congrArg Prod.snd (P.chosenGeodesic_mem (a, b.val)).2) }
  apply (contractible_iff_id_nullhomotopic (P.uniqueTargets a)).mpr
  exact ⟨center, ⟨contraction.symm⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
