import SixVertexUnfolding.Geometry.VertexFanAngles
import SixVertexUnfolding.Geometry.PlanarDirections
import Mathlib.Algebra.BigOperators.Fin

/-! Open the cyclic corner triangles along any original edge ray.
Cumulative angles are ordinary partial sums of the actual sector angles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open EuclideanGeometry Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)

def openingVertex (slit : Fin n) (i : Fin (n + 1)) : P.Vertex :=
  fan.neighbor (slit + ⟨i.val % n, Nat.mod_lt _ (NeZero.pos n)⟩)

noncomputable def openingAngle (slit : Fin n) : Fin (n + 1) → ℝ :=
  Fin.partialSum (fun i => fan.sectorAngle (slit + i))

theorem openingVertex_start (slit i : Fin n) :
    fan.openingVertex slit i.castSucc = fan.neighbor (slit + i) := by
  apply congrArg fan.neighbor
  apply congrArg (fun j : Fin n => slit + j)
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem openingVertex_end (slit i : Fin n) :
    fan.openingVertex slit i.succ = fan.neighbor ((slit + i) + 1) := by
  apply congrArg fan.neighbor
  rw [add_assoc]
  apply congrArg (fun j : Fin n => slit + j)
  apply Fin.ext
  change (i.val + 1) % n = (i.val + 1 % n) % n
  exact (Nat.add_mod _ _ _).trans (by rw [Nat.mod_eq_of_lt i.isLt])

@[simp] theorem openingAngle_zero (slit : Fin n) : fan.openingAngle slit 0 = 0 :=
  Fin.partialSum_zero _

theorem openingAngle_step (slit i : Fin n) :
    fan.openingAngle slit i.succ - fan.openingAngle slit i.castSucc = fan.sectorAngle (slit + i) := by
  rw [openingAngle, Fin.partialSum_succ]
  ring

theorem openingAngle_strictMono (slit : Fin n) : StrictMono (fan.openingAngle slit) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have positive := fan.sectorAngle_pos (slit + i)
  have step := fan.openingAngle_step slit i
  linarith

theorem openingAngle_last (slit : Fin n) : fan.openingAngle slit (Fin.last n) = fan.totalAngle := by
  change ((List.ofFn (fun i => fan.sectorAngle (slit + i))).take n).sum = _
  rw [List.take_of_length_le (by simp), List.sum_ofFn]
  exact Equiv.sum_comp (Equiv.addLeft slit) fan.sectorAngle

theorem openingAngle_nonneg (slit : Fin n) (i : Fin (n + 1)) : 0 ≤ fan.openingAngle slit i := by
  simpa only [fan.openingAngle_zero] using (fan.openingAngle_strictMono slit).monotone (Fin.zero_le i)

theorem openingAngle_le_total (slit : Fin n) (i : Fin (n + 1)) :
    fan.openingAngle slit i ≤ fan.totalAngle := by
  rw [← fan.openingAngle_last slit]
  exact (fan.openingAngle_strictMono slit).monotone (Fin.le_last i)

noncomputable def openingPoint (slit : Fin n) (i : Fin (n + 1)) : Plane :=
  dist (pole : Space) (fan.openingVertex slit i) • direction (fan.openingAngle slit i)

theorem opening_radius_pos (slit : Fin n) (i : Fin (n + 1)) :
    0 < dist (pole : Space) (fan.openingVertex slit i) :=
  dist_pos.mpr (fan.neighbor_ne_pole _).symm

theorem openingPoint_radius (slit : Fin n) (i : Fin (n + 1)) :
    dist 0 (fan.openingPoint slit i) = dist (pole : Space) (fan.openingVertex slit i) :=
  polar_radius _ _ dist_nonneg

theorem openingPoint_base (slit i : Fin n) :
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

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
