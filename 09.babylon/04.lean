symm
apply sum_subset
· rw [subset_iff]
  simp
intro x hx1
intro hx2
simp at hx1
simp at hx2
have hx3 : x < 3
· omega
have h : x = 0 ∨ x = 1 ∨ x = 2
· omega
-- There should be a better way to do the following.
obtain h | h | h := h
· rw [h]
  simp
· rw [h]
  simp
· rw [h]
  simp
