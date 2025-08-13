unfold range fixedPoints IsFixedPt
ext a
constructor
· intro ⟨x, hx⟩
  rw [← hx]
  simp
  trans (f ∘ f) x
  · apply comp_apply
  · rw [h]
· simp
  intro ha
  use a
