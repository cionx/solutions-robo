rw [subset_iff]
intro b hb
obtain ⟨a, ha₁, ha₂⟩ := hb
simp at ha₁
rw [← ha₂]
assumption
