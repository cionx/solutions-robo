have cantor_diagonal_contra {A Y}
  (s : Y → Y) (hs : ¬ ∃ y : Y, IsFixedPt s y) :
  ∀ (f : A → A → Y), ¬ Surjective f
. intro f hf
  have hp := cantor_diagonal f hf s
  obtain ⟨p, hp⟩ := hp
  push_neg at hs
  apply hs at hp
  assumption

let s (n : ℕ) := n + 1
have s_no_fp : ¬ ∃ n : ℕ, IsFixedPt s n
· simp [s]
  unfold IsFixedPt
  simp

have h {A} (f : A → A → ℕ) := cantor_diagonal_contra s s_no_fp f
push_neg
apply h
