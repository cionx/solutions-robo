intro ⟨f, hf⟩
let s (p : Prop) := ¬ p
have hp := cantor_diagonal f hf s
simp at hp
obtain ⟨p, hp⟩ := hp
unfold IsFixedPt at hp
simp [s] at hp
