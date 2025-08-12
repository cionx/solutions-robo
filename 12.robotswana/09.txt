have h₃ : f 1 = ∑ i : Fin n, f (E i i)
· rw [← ebasis_diag_sum_eq_one]
  simp

intro j

have h₄ : ∀ i : Fin n, f (E i i) = f (E j j)
· intro i
  apply eq_on_diag_ebasis h₁

have h₅ : ↑1 = f (E j j)
· rw [h₃] at h₂
  simp [h₄] at h₂
  suffices h : ↑n * f (E j j) = ↑ n * 1
  · rw [mul_eq_mul_left_iff] at h
    obtain h | h := h
    · symm
      assumption
    · simp at h
      omega
  · rw [h₂]
    simp

symm
assumption
