intro h3
rw [dvd_iff_exists_eq_mul_left] at h3
obtain ⟨l, h3⟩ := h3
rw [mul_comm] at h3
have h4 : k < l
· rw [h3] at h1
  apply lt_of_mul_lt_mul_left at h1
  omega
have h5 : l < k + 1
· rw [h3] at h2
  apply lt_of_mul_lt_mul_left at h2
  omega
omega
