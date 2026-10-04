import SixVertexUnfolding.Geometry.ThreeCornerCones
import SixVertexUnfolding.Geometry.FourCornerCones

/-! Read an outward fan from its other end, without changing its placed polygons. -/

namespace SixVertexUnfolding

open EuclideanGeometry

namespace ThreeTriangleChain

/-- Reversing the list preserves the same outward hinges. -/
def reverse (chain : ThreeTriangleChain) : ThreeTriangleChain where
  center := chain.center
  ray i := chain.ray i.rev
  noncollinear := by
    intro i
    fin_cases i
    · change ¬ Collinear ℝ ({chain.center, chain.ray 3, chain.ray 2} : Set Plane)
      simpa only [Set.pair_comm] using chain.noncollinear 2
    · change ¬ Collinear ℝ ({chain.center, chain.ray 2, chain.ray 1} : Set Plane)
      simpa only [Set.pair_comm] using chain.noncollinear 1
    · change ¬ Collinear ℝ ({chain.center, chain.ray 1, chain.ray 0} : Set Plane)
      simpa only [Set.pair_comm] using chain.noncollinear 0
  outward := by
    intro i
    fin_cases i
    · change OppositeHingeSides chain.center (chain.ray 2) (chain.ray 3) (chain.ray 1)
      simpa only [OppositeHingeSides, real_inner_comm] using chain.outward 1
    · change OppositeHingeSides chain.center (chain.ray 1) (chain.ray 2) (chain.ray 0)
      simpa only [OppositeHingeSides, real_inner_comm] using chain.outward 0

@[simp] theorem reverse_corner (chain : ThreeTriangleChain) (i : Fin 3) :
    chain.reverse.corner i = chain.corner i.rev := by
  fin_cases i <;> exact angle_comm _ _ _

/-- The reversed corner is exactly the original cone, with its two generators exchanged. -/
@[simp] theorem reverse_cornerCone (chain : ThreeTriangleChain) (i : Fin 3) :
    chain.reverse.cornerCone i = chain.cornerCone i.rev := by
  ext x
  fin_cases i <;> constructor <;> rintro ⟨t, u, ht, hu, coords⟩ <;>
    exact ⟨u, t, hu, ht, coords.trans (add_comm _ _)⟩

/-- Reversing the fan leaves its total angle unchanged. -/
theorem reverse_angle_sum (chain : ThreeTriangleChain) :
    (∑ i, chain.reverse.corner i) = ∑ i, chain.corner i := by
  simp only [Fin.sum_univ_three, reverse_corner]
  change chain.corner 2 + chain.corner 1 + chain.corner 0 = chain.corner 0 + chain.corner 1 + chain.corner 2
  ring

end ThreeTriangleChain

namespace FourTriangleChain

/-- Reversing the list preserves the same outward hinges. -/
def reverse (chain : FourTriangleChain) : FourTriangleChain where
  center := chain.center
  ray i := chain.ray i.rev
  noncollinear := by
    intro i
    fin_cases i
    · change ¬ Collinear ℝ ({chain.center, chain.ray 4, chain.ray 3} : Set Plane)
      simpa only [Set.pair_comm] using chain.noncollinear 3
    · change ¬ Collinear ℝ ({chain.center, chain.ray 3, chain.ray 2} : Set Plane)
      simpa only [Set.pair_comm] using chain.noncollinear 2
    · change ¬ Collinear ℝ ({chain.center, chain.ray 2, chain.ray 1} : Set Plane)
      simpa only [Set.pair_comm] using chain.noncollinear 1
    · change ¬ Collinear ℝ ({chain.center, chain.ray 1, chain.ray 0} : Set Plane)
      simpa only [Set.pair_comm] using chain.noncollinear 0
  outward := by
    intro i
    fin_cases i
    · change OppositeHingeSides chain.center (chain.ray 3) (chain.ray 4) (chain.ray 2)
      simpa only [OppositeHingeSides, real_inner_comm] using chain.outward 2
    · change OppositeHingeSides chain.center (chain.ray 2) (chain.ray 3) (chain.ray 1)
      simpa only [OppositeHingeSides, real_inner_comm] using chain.outward 1
    · change OppositeHingeSides chain.center (chain.ray 1) (chain.ray 2) (chain.ray 0)
      simpa only [OppositeHingeSides, real_inner_comm] using chain.outward 0

@[simp] theorem reverse_corner (chain : FourTriangleChain) (i : Fin 4) :
    chain.reverse.corner i = chain.corner i.rev := by
  fin_cases i <;> exact angle_comm _ _ _

/-- The reversed corner is exactly the original cone, with its two generators exchanged. -/
@[simp] theorem reverse_cornerCone (chain : FourTriangleChain) (i : Fin 4) :
    chain.reverse.cornerCone i = chain.cornerCone i.rev := by
  ext x
  fin_cases i <;> constructor <;> rintro ⟨t, u, ht, hu, coords⟩ <;>
    exact ⟨u, t, hu, ht, coords.trans (add_comm _ _)⟩

/-- Reversing the fan leaves its total angle unchanged. -/
theorem reverse_angle_sum (chain : FourTriangleChain) :
    (∑ i, chain.reverse.corner i) = ∑ i, chain.corner i := by
  simp only [Fin.sum_univ_four, reverse_corner]
  change chain.corner 3 + chain.corner 2 + chain.corner 1 + chain.corner 0 = chain.corner 0 + chain.corner 1 + chain.corner 2 + chain.corner 3
  ring

end FourTriangleChain

end SixVertexUnfolding
