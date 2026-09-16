import SixVertexUnfolding.Geometry.FiveFaceFan
import SixVertexUnfolding.Geometry.PlanarDirections

/-! Open the five incident faces along any one of their radial edges. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan

open EuclideanGeometry Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} (fan : P.FiveFaceFan pole)

/-- The first and last entries are the two copies of the slit ray. -/
def openingVertex (slit : Fin 5) (i : Fin 6) : P.Vertex :=
  fan.neighbor (slit + ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩)

noncomputable def openingAngle (slit : Fin 5) : Fin 6 → ℝ :=
  ![0, fan.sectorAngle slit,
    fan.sectorAngle slit + fan.sectorAngle (slit + 1),
    fan.sectorAngle slit + fan.sectorAngle (slit + 1) + fan.sectorAngle (slit + 2),
    fan.sectorAngle slit + fan.sectorAngle (slit + 1) + fan.sectorAngle (slit + 2) +
      fan.sectorAngle (slit + 3),
    fan.sectorAngle slit + fan.sectorAngle (slit + 1) + fan.sectorAngle (slit + 2) +
      fan.sectorAngle (slit + 3) + fan.sectorAngle (slit + 4)]

theorem openingVertex_start (slit i : Fin 5) :
    fan.openingVertex slit i.castSucc = fan.neighbor (slit + i) := by
  apply congrArg fan.neighbor
  apply congrArg (fun j : Fin 5 => slit + j)
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem openingVertex_end (slit i : Fin 5) :
    fan.openingVertex slit i.succ = fan.neighbor ((slit + i) + 1) := by
  apply congrArg fan.neighbor
  rw [add_assoc]
  apply congrArg (fun j : Fin 5 => slit + j)
  exact Fin.ext rfl

theorem openingAngle_step (slit i : Fin 5) :
    fan.openingAngle slit i.succ - fan.openingAngle slit i.castSucc = fan.sectorAngle (slit + i) := by
  fin_cases i <;> simp [openingAngle]

theorem openingAngle_strictMono (slit : Fin 5) : StrictMono (fan.openingAngle slit) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have positive := fan.sectorAngle_pos (slit + i)
  have step := fan.openingAngle_step slit i
  linarith

theorem openingAngle_last (slit : Fin 5) : fan.openingAngle slit 5 = fan.totalAngle := by
  fin_cases slit <;> simp [openingAngle, totalAngle, Fin.sum_univ_succ] <;> ring

theorem openingAngle_nonneg (slit : Fin 5) (i : Fin 6) : 0 ≤ fan.openingAngle slit i :=
  (fan.openingAngle_strictMono slit).monotone (Fin.zero_le i)

theorem openingAngle_le_total (slit : Fin 5) (i : Fin 6) :
    fan.openingAngle slit i ≤ fan.totalAngle := by
  rw [← fan.openingAngle_last slit]
  exact (fan.openingAngle_strictMono slit).monotone (by omega : i ≤ (5 : Fin 6))

noncomputable def openingPoint (slit : Fin 5) (i : Fin 6) : Plane :=
  dist (pole : Space) (fan.openingVertex slit i) • direction (fan.openingAngle slit i)

theorem opening_radius_pos (slit : Fin 5) (i : Fin 6) :
    0 < dist (pole : Space) (fan.openingVertex slit i) :=
  dist_pos.mpr (fan.neighbor_ne_pole _).symm

theorem openingPoint_radius (slit : Fin 5) (i : Fin 6) :
    dist 0 (fan.openingPoint slit i) = dist (pole : Space) (fan.openingVertex slit i) :=
  polar_radius _ _ dist_nonneg

theorem openingPoint_base (slit i : Fin 5) :
    dist (fan.openingPoint slit i.castSucc) (fan.openingPoint slit i.succ) =
      dist (fan.neighbor (slit + i) : Space) (fan.neighbor ((slit + i) + 1)) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [openingPoint, openingPoint, polar_distance_sq, fan.openingAngle_step,
    fan.openingVertex_start, fan.openingVertex_end]
  have cosine_law := law_cos (fan.neighbor (slit + i) : Space) (pole : Space)
    (fan.neighbor ((slit + i) + 1))
  simp only [← sq, dist_comm (fan.neighbor (slit + i) : Space) (pole : Space),
    dist_comm (fan.neighbor ((slit + i) + 1) : Space) (pole : Space)] at cosine_law
  exact cosine_law.symm

end SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan
