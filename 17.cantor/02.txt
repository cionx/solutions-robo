-- Copied from the previous level.
have prev (f : A → Set A) : ¬ ∃ (a : A), f a = { x | x ∉ f x }
· by_contra h
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
-- Copy end.

by_contra h
obtain ⟨f, hf⟩ := h
let S := { x : A | x ∉ f x }
unfold Surjective at hf
obtain ⟨a, ha⟩ := hf S
tauto
