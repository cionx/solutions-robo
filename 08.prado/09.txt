rw [dvd_iff_exists_eq_mul_left] at h
obtain ⟨k, h⟩ := h
use k
simp
constructor
· rw [h]
  apply mul_comm
· intro l hl
  rw [mul_comm] at h
  rw [← hl] at h
  rw [mul_eq_mul_left_iff] at h
  obtain h | h := h
  · assumption
  · omega
