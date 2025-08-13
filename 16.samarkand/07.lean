unfold LeftInverse at hL
rw [subset_iff]
simp
intro a ha
suffices h : g (f a) = a
· rw [h]
  assumption
· apply hL a
