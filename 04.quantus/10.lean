by_cases ∀ (y : People), isDrinking y
· obtain ⟨p⟩ := h_nonempty
  use p
  intro
  assumption
· push_neg at h
  obtain ⟨p, hnp⟩ := h
  use p
  intro hp
  contradiction
