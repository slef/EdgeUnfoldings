import SixVertexUnfolding.Geometry.TreeDevelopment

/-! Identifying subdivision pieces preserves connectedness; a spanning tree then uses only surviving hinges. -/

namespace SixVertexUnfolding

/-- Retain precisely the hinges joining different original faces. -/
def contractedHinges {V W : Type*} (hinges : SimpleGraph V) (face : V → W) : SimpleGraph W where
  Adj a b := a ≠ b ∧ ∃ x y, hinges.Adj x y ∧ face x = a ∧ face y = b
  symm := by
    rintro a b ⟨different, x, y, edge, rfl, rfl⟩
    exact ⟨different.symm, y, x, edge.symm, rfl, rfl⟩
  loopless := ⟨fun _ edge => edge.1 rfl⟩

/-- A subdivision walk gives a face walk after omitting the steps internal to one face. -/
theorem contractedHinges_reachable {V W : Type*} (hinges : SimpleGraph V) (face : V → W)
    {a b : V} (reachable : hinges.Reachable a b) :
    (contractedHinges hinges face).Reachable (face a) (face b) := by
  obtain ⟨walk⟩ := reachable
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b edge rest induction =>
      by_cases same : face a = face c
      · rwa [same]
      · exact (show (contractedHinges hinges face).Adj (face a) (face c) from
          ⟨same, a, c, edge, rfl, rfl⟩).reachable.trans induction

/-- Every original face is reached when its subdivision pieces are connected. -/
theorem contractedHinges_connected {V W : Type*} (hinges : SimpleGraph V) (face : V → W)
    (connected : hinges.Connected) (onto : Function.Surjective face) :
    (contractedHinges hinges face).Connected := by
  haveI : Nonempty V := connected.nonempty
  haveI : Nonempty W := Nonempty.map face inferInstance
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := onto a
  obtain ⟨y, rfl⟩ := onto b
  exact contractedHinges_reachable hinges face (connected x y)

end SixVertexUnfolding
