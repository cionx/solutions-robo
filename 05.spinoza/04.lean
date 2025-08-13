constructor
· intro h
  intro nb
  intro a
  apply nb
  apply h
  assumption
· intro h₁
  intro a
  by_cases h₂ : B
  · assumption
  · apply h₁ at h₂
    contradiction
