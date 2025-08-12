unfold Function.RightInverse Function.LeftInverse
constructor
· intro h
  funext
  simp
  apply h x
· intro h
  intro x
  trans (f ∘ g) x
  · rw [← comp_apply (f:=f)]
  · rw [h]
    simp
