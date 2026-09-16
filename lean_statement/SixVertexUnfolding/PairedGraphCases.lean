import Mathlib

/-! Finite propositional classification after three nonedge pairs have been fixed. -/

namespace SixVertexUnfolding.SmallGraphs

set_option maxHeartbeats 2000000 in
/-- Extra nonedges form a matching; excluding four-cycles leaves these 45 explicit patterns. -/
theorem paired_graph_propositional_cases
    (e02 e03 e04 e05 e12 e13 e14 e15 e24 e25 e34 e35 : Prop)
    (matching : ¬ (e02 ∧ e03) ∧
      ¬ (e02 ∧ e04) ∧
      ¬ (e02 ∧ e05) ∧
      ¬ (e02 ∧ e12) ∧
      ¬ (e02 ∧ e24) ∧
      ¬ (e02 ∧ e25) ∧
      ¬ (e03 ∧ e04) ∧
      ¬ (e03 ∧ e05) ∧
      ¬ (e03 ∧ e13) ∧
      ¬ (e03 ∧ e34) ∧
      ¬ (e03 ∧ e35) ∧
      ¬ (e04 ∧ e05) ∧
      ¬ (e04 ∧ e14) ∧
      ¬ (e04 ∧ e24) ∧
      ¬ (e04 ∧ e34) ∧
      ¬ (e05 ∧ e15) ∧
      ¬ (e05 ∧ e25) ∧
      ¬ (e05 ∧ e35) ∧
      ¬ (e12 ∧ e13) ∧
      ¬ (e12 ∧ e14) ∧
      ¬ (e12 ∧ e15) ∧
      ¬ (e12 ∧ e24) ∧
      ¬ (e12 ∧ e25) ∧
      ¬ (e13 ∧ e14) ∧
      ¬ (e13 ∧ e15) ∧
      ¬ (e13 ∧ e34) ∧
      ¬ (e13 ∧ e35) ∧
      ¬ (e14 ∧ e15) ∧
      ¬ (e14 ∧ e24) ∧
      ¬ (e14 ∧ e34) ∧
      ¬ (e15 ∧ e25) ∧
      ¬ (e15 ∧ e35) ∧
      ¬ (e24 ∧ e25) ∧
      ¬ (e24 ∧ e34) ∧
      ¬ (e25 ∧ e35) ∧
      ¬ (e34 ∧ e35))
    (no_square : ¬ (e02 ∧ e13) ∧
      ¬ (e03 ∧ e12) ∧
      ¬ (e04 ∧ e15) ∧
      ¬ (e05 ∧ e14) ∧
      ¬ (e24 ∧ e35) ∧
      ¬ (e25 ∧ e34)) :
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ e35) ∨
    (e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ e34 ∧ ¬ e35) ∨
    (e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ e35) ∨
    (¬ e02 ∧ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ e04 ∧ ¬ e05 ∧ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ e05 ∧ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ e05 ∧ ¬ e12 ∧ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ e15 ∧ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ e34 ∧ ¬ e35) ∨
    (e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ e35) ∨
    (e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ e15 ∧ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ e04 ∧ ¬ e05 ∧ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ e25 ∧ ¬ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ e05 ∧ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e25 ∧ e34 ∧ ¬ e35) ∨
    (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ e05 ∧ ¬ e12 ∧ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ e24 ∧ ¬ e25 ∧ ¬ e34 ∧ ¬ e35) := by
  classical
  rcases matching with ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35⟩
  rcases no_square with ⟨q0, q1, q2, q3, q4, q5⟩
  by_cases he02 : e02
  · have he03 : ¬ e03 := fun other => m0 ⟨he02, other⟩
    have he04 : ¬ e04 := fun other => m1 ⟨he02, other⟩
    have he05 : ¬ e05 := fun other => m2 ⟨he02, other⟩
    have he12 : ¬ e12 := fun other => m3 ⟨he02, other⟩
    have he13 : ¬ e13 := fun other => q0 ⟨he02, other⟩
    have he24 : ¬ e24 := fun other => m4 ⟨he02, other⟩
    have he25 : ¬ e25 := fun other => m5 ⟨he02, other⟩
    by_cases he14 : e14
    · have he15 : ¬ e15 := fun other => m27 ⟨he14, other⟩
      have he34 : ¬ e34 := fun other => m29 ⟨he14, other⟩
      by_cases he35 : e35
      · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
      · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
    · by_cases he15 : e15
      · have he35 : ¬ e35 := fun other => m31 ⟨he15, other⟩
        by_cases he34 : e34
        · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
        · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
      · by_cases he34 : e34
        · have he35 : ¬ e35 := fun other => m35 ⟨he34, other⟩
          simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
        · by_cases he35 : e35
          · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
          · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
  · by_cases he03 : e03
    · have he04 : ¬ e04 := fun other => m6 ⟨he03, other⟩
      have he05 : ¬ e05 := fun other => m7 ⟨he03, other⟩
      have he12 : ¬ e12 := fun other => q1 ⟨he03, other⟩
      have he13 : ¬ e13 := fun other => m8 ⟨he03, other⟩
      have he34 : ¬ e34 := fun other => m9 ⟨he03, other⟩
      have he35 : ¬ e35 := fun other => m10 ⟨he03, other⟩
      by_cases he14 : e14
      · have he15 : ¬ e15 := fun other => m27 ⟨he14, other⟩
        have he24 : ¬ e24 := fun other => m28 ⟨he14, other⟩
        by_cases he25 : e25
        · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
        · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
      · by_cases he15 : e15
        · have he25 : ¬ e25 := fun other => m30 ⟨he15, other⟩
          by_cases he24 : e24
          · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
          · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
        · by_cases he24 : e24
          · have he25 : ¬ e25 := fun other => m32 ⟨he24, other⟩
            simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
          · by_cases he25 : e25
            · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
            · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
    · by_cases he04 : e04
      · have he05 : ¬ e05 := fun other => m11 ⟨he04, other⟩
        have he14 : ¬ e14 := fun other => m12 ⟨he04, other⟩
        have he15 : ¬ e15 := fun other => q2 ⟨he04, other⟩
        have he24 : ¬ e24 := fun other => m13 ⟨he04, other⟩
        have he34 : ¬ e34 := fun other => m14 ⟨he04, other⟩
        by_cases he12 : e12
        · have he13 : ¬ e13 := fun other => m18 ⟨he12, other⟩
          have he25 : ¬ e25 := fun other => m22 ⟨he12, other⟩
          by_cases he35 : e35
          · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
          · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
        · by_cases he13 : e13
          · have he35 : ¬ e35 := fun other => m26 ⟨he13, other⟩
            by_cases he25 : e25
            · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
            · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
          · by_cases he25 : e25
            · have he35 : ¬ e35 := fun other => m34 ⟨he25, other⟩
              simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
            · by_cases he35 : e35
              · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
              · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
      · by_cases he05 : e05
        · have he14 : ¬ e14 := fun other => q3 ⟨he05, other⟩
          have he15 : ¬ e15 := fun other => m15 ⟨he05, other⟩
          have he25 : ¬ e25 := fun other => m16 ⟨he05, other⟩
          have he35 : ¬ e35 := fun other => m17 ⟨he05, other⟩
          by_cases he12 : e12
          · have he13 : ¬ e13 := fun other => m18 ⟨he12, other⟩
            have he24 : ¬ e24 := fun other => m21 ⟨he12, other⟩
            by_cases he34 : e34
            · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
            · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
          · by_cases he13 : e13
            · have he34 : ¬ e34 := fun other => m25 ⟨he13, other⟩
              by_cases he24 : e24
              · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
              · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
            · by_cases he24 : e24
              · have he34 : ¬ e34 := fun other => m33 ⟨he24, other⟩
                simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
              · by_cases he34 : e34
                · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
        · by_cases he12 : e12
          · have he13 : ¬ e13 := fun other => m18 ⟨he12, other⟩
            have he14 : ¬ e14 := fun other => m19 ⟨he12, other⟩
            have he15 : ¬ e15 := fun other => m20 ⟨he12, other⟩
            have he24 : ¬ e24 := fun other => m21 ⟨he12, other⟩
            have he25 : ¬ e25 := fun other => m22 ⟨he12, other⟩
            by_cases he34 : e34
            · have he35 : ¬ e35 := fun other => m35 ⟨he34, other⟩
              simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
            · by_cases he35 : e35
              · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
              · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
          · by_cases he13 : e13
            · have he14 : ¬ e14 := fun other => m23 ⟨he13, other⟩
              have he15 : ¬ e15 := fun other => m24 ⟨he13, other⟩
              have he34 : ¬ e34 := fun other => m25 ⟨he13, other⟩
              have he35 : ¬ e35 := fun other => m26 ⟨he13, other⟩
              by_cases he24 : e24
              · have he25 : ¬ e25 := fun other => m32 ⟨he24, other⟩
                simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
              · by_cases he25 : e25
                · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
            · by_cases he14 : e14
              · have he15 : ¬ e15 := fun other => m27 ⟨he14, other⟩
                have he24 : ¬ e24 := fun other => m28 ⟨he14, other⟩
                have he34 : ¬ e34 := fun other => m29 ⟨he14, other⟩
                by_cases he25 : e25
                · have he35 : ¬ e35 := fun other => m34 ⟨he25, other⟩
                  simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                · by_cases he35 : e35
                  · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                  · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
              · by_cases he15 : e15
                · have he25 : ¬ e25 := fun other => m30 ⟨he15, other⟩
                  have he35 : ¬ e35 := fun other => m31 ⟨he15, other⟩
                  by_cases he24 : e24
                  · have he34 : ¬ e34 := fun other => m33 ⟨he24, other⟩
                    simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                  · by_cases he34 : e34
                    · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                    · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                · by_cases he24 : e24
                  · have he25 : ¬ e25 := fun other => m32 ⟨he24, other⟩
                    have he34 : ¬ e34 := fun other => m33 ⟨he24, other⟩
                    have he35 : ¬ e35 := fun other => q4 ⟨he24, other⟩
                    simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                  · by_cases he25 : e25
                    · have he34 : ¬ e34 := fun other => q5 ⟨he25, other⟩
                      have he35 : ¬ e35 := fun other => m34 ⟨he25, other⟩
                      simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                    · by_cases he34 : e34
                      · have he35 : ¬ e35 := fun other => m35 ⟨he34, other⟩
                        simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                      · by_cases he35 : e35
                        · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]
                        · simp [he02, he03, he04, he05, he12, he13, he14, he15, he24, he25, he34, he35]

end SixVertexUnfolding.SmallGraphs
