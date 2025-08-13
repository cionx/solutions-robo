obtain ⟨g, hg⟩ := h
unfold LeftInverse at hg
unfold Injective
intro a₁ a₂ hf
apply congr_arg g at hf
rw [hg] at hf
rw [hg] at hf
assumption
