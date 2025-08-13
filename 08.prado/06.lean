rw [prime_def] at hp
obtain ⟨h1, h2⟩ := hp
specialize h2 a ha
obtain h2 | h2 := h2
· rw [h2] at h
  contradiction
· assumption
