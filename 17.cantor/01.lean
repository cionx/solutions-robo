by_contra h
obtain ⟨a, ha⟩ := h

have h : a ∈ f a ↔ a ∉ f a
· constructor
  · intro h
    rw [ha] at h
    simp at h
    assumption
  · intro h
    rw [ha] at h
    simp at h
    assumption

tauto
