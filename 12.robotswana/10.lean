funext A
rw [eq_sum_apply_diag_ebasis h₁]
unfold trace Matrix.diag
rw [sum_congr rfl]
simp
intro i
suffices h : f (E i i) = 1
· rw [h]
  simp
· by_cases h₃ : n = 0
  · have h₄ : i < n := by simp
    linarith
  · have h₄ : n > 0 := by omega
    apply one_on_diag_ebasis h₄ h₁ h₂
