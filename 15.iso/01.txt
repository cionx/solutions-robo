constructor
· apply StrictMono.injective
  unfold StrictMono
  simp [f]
· unfold Surjective
  intro b
  use b - 1
  simp [f]
