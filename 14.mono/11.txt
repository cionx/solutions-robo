-- We need to combine the previous two levels.

have has_left_inv_imp_inj (f : A → B) (h : HasLeftInverse f) : Injective f
· obtain ⟨g, hg⟩ := h
  unfold LeftInverse at hg
  unfold Injective
  intro a₁ a₂ hf
  apply congr_arg g at hf
  rw [hg] at hf
  rw [hg] at hf
  assumption

have preim_func (f : A → B ) : ∀ b : B, ∃ a : A, f a = b ∨ ¬ ∃ a' : A , f a' = b
· intro b
  by_cases h : ∃ a : A, f a = b
  · obtain ⟨a, ha⟩ := h
    use a
    tauto
  · obtain ⟨a⟩ := hA
    use a
    tauto

constructor
· intro hf
  choose g hg using preim_func f
  use g
  unfold LeftInverse
  intro a
  apply hf
  have h := hg (f a)
  obtain h | h := h
  · assumption
  · tauto
· apply has_left_inv_imp_inj
