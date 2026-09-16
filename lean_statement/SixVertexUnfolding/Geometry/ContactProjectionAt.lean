import SixVertexUnfolding.Geometry.ContactProjection

/-! The contact projection inequality in arbitrary planar coordinates. -/

namespace SixVertexUnfolding.Contact

theorem contact_metric_obtuse_at (a w m p : Plane) (m_ne : m ≠ a)
    (equal_radius : dist p a = dist m a) (different : m ≠ p)
    (t : ℝ) (lower : 0 ≤ t) (upper : t ≤ 1)
    (contained : m ∈ convexHull ℝ ({a, w, a + t • (p - a)} : Set Plane)) (not_w : m ≠ w) :
    dist m a ^ 2 + dist w m ^ 2 < dist w a ^ 2 := by
  let shift : Plane →ᵃ[ℝ] Plane := (AffineEquiv.vaddConst ℝ (-a)).toAffineMap
  have shift_apply (z : Plane) : shift z = z - a := by simp [shift, sub_eq_add_neg]
  have at_contact : shift (a + t • (p - a)) = t • (p - a) := by rw [shift_apply]; module
  have shifted : m - a ∈ convexHull ℝ ({0, w - a, t • (p - a)} : Set Plane) := by
    have member := Set.mem_image_of_mem shift contained
    rw [shift.image_convexHull, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      at_contact, shift_apply, shift_apply, shift_apply, sub_self] at member
    exact member
  have strict := contact_metric_obtuse (w - a) (m - a) (p - a) (sub_ne_zero.mpr m_ne)
    (by simpa only [dist_eq_norm] using equal_radius)
    (fun same => different (by simpa only [sub_add_cancel] using congrArg (fun z : Plane => z + a) same)) t lower upper shifted
    (fun same => not_w (by simpa only [sub_add_cancel] using congrArg (fun z : Plane => z + a) same))
  have cancel : (w - a) - (m - a) = w - m := by module
  rw [cancel] at strict
  simpa only [dist_eq_norm] using strict

end SixVertexUnfolding.Contact
