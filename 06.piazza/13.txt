ext x
simp
constructor
· intro h1
  obtain h2 | ⟨h3, h4⟩ := h1
  · rw [h2]
    assumption
  · assumption
· intro hx
  by_cases heq : x = a
  · left
    assumption
  · right
    constructor
    · assumption
    · assumption
