rw [dvd_iff_exists_eq_mul_left] at *
obtain ⟨k₁, h₁⟩ := h
obtain ⟨k₂, h₂⟩ := g
use k₁ + k₂
rw [h₁, h₂]
ring
