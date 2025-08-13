have in_Icc_left (a b : ℕ) (h : a ≤ b) : a ∈ Icc a b
· simp
  assumption

have in_Icc_right (a b : ℕ) (h : a ≤ b) : b ∈ Icc a b
· simp
  assumption

intro h₁
rw [subset_iff]
constructor
· intro h₂
  constructor
  · have h₃ := h₂ (in_Icc_left a₁ b₁ h₁)
    simp at h₃
    omega
  · have h₃ := h₂ (in_Icc_right a₁ b₁ h₁)
    simp at h₃
    omega
· intro ⟨h₂, h₃⟩
  intro x hx
  simp at hx
  obtain ⟨h₄, h₅⟩ := hx
  simp
  omega
