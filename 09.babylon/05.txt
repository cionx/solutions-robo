trans ∑ i ∈ {i ∈ I | Even i}, ((-1)^i + 1)
· symm
  apply sum_subset
  · simp
  · intro x 
    intro hx1 hx2
    simp at hx2
    apply hx2 at hx1
    rw [← odd_iff_not_even] at hx1
    rw [Odd.neg_pow hx1]
    simp
· trans ∑ i ∈ {i ∈ I | Even i}, 2
  · apply sum_congr
    · rfl
    · intro x hx
      simp at hx
      obtain ⟨_, he⟩ := hx
      rw [Even.neg_pow he]
      simp
  · simp
    ring
