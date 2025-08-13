intro b
by_cases h : ∃ a : A, f a = b
· obtain ⟨a, ha⟩ := h
  use a
  tauto
· obtain ⟨a⟩ := hA
  use a
  tauto
