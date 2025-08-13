intro a b
by_cases h1 : a ≤ b
· by_cases h2 : a < b
  · left
    assumption
  · rw [← not_le] at h2
    rw [not_not] at h2
    right
    left
    linarith
· rw [not_le] at h1
  right
  right
  assumption
