ext S c
constructor
· intro hc
  obtain ⟨a, ha₁, ha₂⟩ := hc
  simp
  use a
  constructor
  · assumption
  · simp at ha₂
    assumption
· intro hc
  obtain ⟨b, h₁, h₂⟩ := hc
  simp at h₁
  obtain ⟨a, ha₁, ha₂⟩ := h₁
  rw [← ha₂] at h₂
  simp
  use a
