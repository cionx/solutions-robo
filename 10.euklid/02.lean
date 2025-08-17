-- div_mul_left is already used by the background library
have div_mul_left2 {a b : ℕ} : a ∣ a * b := by use b

have div_prod {a : ℕ} {A : Finset ℕ} (h : a ∈ A) : a ∣ ∏ a ∈ A, a
· rw [← insert_erase h]
  rw [prod_insert]
  · apply div_mul_left2
  · simp

have div_trans {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c
· obtain ⟨r, hr⟩ := h1
  obtain ⟨s, hs⟩ := h2
  rw [hs]
  rw [hr]
  use r * s
  ring

intro ⟨a, ha, hp⟩
apply div_prod at ha
apply div_trans hp ha
