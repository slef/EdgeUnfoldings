import SixVertexUnfolding.Geometry.CutEdgeTriangles
import SixVertexUnfolding.Geometry.TwoBranchUniqueness

/-! Independently chosen route branches at opposite ends of an edge
agree along the entire edge, up to one fixed swap of the two labels. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Reverse the open edge parameter, retaining the open interval. -/
noncomputable def reverseInteriorTime : C(Ioo (0 : ℝ) 1, Ioo (0 : ℝ) 1) :=
  ⟨fun t => ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩,
    by fun_prop⟩

theorem reverseInteriorTime_interiorTime (t : Ioo (0 : ℝ) 1) :
    interiorTime (reverseInteriorTime t) = unitInterval.symm (interiorTime t) := rfl

namespace CutLocusTree

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

theorem openEdgeTarget_reverse {u v : T.vertices} (edge : T.graph.Adj u v) (t : Ioo (0 : ℝ) 1) :
    T.openEdgeTarget edge.symm (reverseInteriorTime t) = T.openEdgeTarget edge t := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one_sub (v : Space) (u : Space) (t : ℝ)

theorem closedEdgeTarget_reverse {u v : T.vertices} (edge : T.graph.Adj u v) (t : unitInterval) :
    T.closedEdgeTarget edge.symm (unitInterval.symm t) = T.closedEdgeTarget edge t := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one_sub (v : Space) (u : Space) (t : ℝ)

end CutLocusTree

namespace CutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}
    (D : CutEdgeTriangles T edge) (E : CutEdgeTriangles T edge.symm)

/-- There is one consistent branch correspondence, including both endpoint limits. -/
theorem reversed_route_families :
    ((∀ t, D.first t = E.first (unitInterval.symm t)) ∧
      (∀ t, D.second t = E.second (unitInterval.symm t))) ∨
    ((∀ t, D.first t = E.second (unitInterval.symm t)) ∧
      (∀ t, D.second t = E.first (unitInterval.symm t))) := by
  letI : PreconnectedSpace (Ioo (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
  have selected (t : Ioo (0 : ℝ) 1) :
      D.strips.first t = E.strips.first (reverseInteriorTime t) ∨
        D.strips.first t = E.strips.second (reverseInteriorTime t) := by
    have member := D.strips.first_member t
    rw [← T.openEdgeTarget_reverse edge t, E.strips.fiber] at member
    exact member
  have extend (f g : C(unitInterval, P.BoundaryCurve))
      (agrees : ∀ t, f (interiorTime t) = g (unitInterval.symm (interiorTime t))) :
      ∀ t, f t = g (unitInterval.symm t) := by
    have equal := interiorTime_dense.equalizer f.continuous
      (g.continuous.comp unitInterval.continuous_symm) (funext agrees)
    exact congrFun equal
  have other_member (t : Ioo (0 : ℝ) 1) :
      D.strips.second t = E.strips.first (reverseInteriorTime t) ∨
        D.strips.second t = E.strips.second (reverseInteriorTime t) := by
    have member := D.strips.second_member t
    rw [← T.openEdgeTarget_reverse edge t, E.strips.fiber] at member
    exact member
  rcases continuous_two_branch_choice D.strips.first
      (fun t => E.strips.first (reverseInteriorTime t))
      (fun t => E.strips.second (reverseInteriorTime t))
      D.strips.first.continuous (E.strips.first.continuous.comp reverseInteriorTime.continuous)
      (E.strips.second.continuous.comp reverseInteriorTime.continuous)
      (fun t => E.strips.distinct (reverseInteriorTime t)) selected with first | second
  · left
    constructor
    · apply extend D.first E.first
      intro t
      rw [(D.agrees t).1, ← reverseInteriorTime_interiorTime, (E.agrees _).1]
      exact congrFun first t
    · apply extend D.second E.second
      intro t
      rw [(D.agrees t).2, ← reverseInteriorTime_interiorTime, (E.agrees _).2]
      exact (other_member t).resolve_left (fun same => D.strips.distinct t ((congrFun first t).trans same.symm))
  · right
    constructor
    · apply extend D.first E.second
      intro t
      rw [(D.agrees t).1, ← reverseInteriorTime_interiorTime, (E.agrees _).2]
      exact congrFun second t
    · apply extend D.second E.first
      intro t
      rw [(D.agrees t).2, ← reverseInteriorTime_interiorTime, (E.agrees _).1]
      exact (other_member t).resolve_right (fun same => D.strips.distinct t ((congrFun second t).trans same.symm))

end CutEdgeTriangles
end SixVertexUnfolding.ConvexPolyhedron
