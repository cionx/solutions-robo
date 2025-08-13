use 2
simp
constructor
· decide
· intro p hp he
  rw [even_iff_two_dvd] at he
  rw [prime_def] at hp
  obtain ⟨h2, hp⟩ := hp
  specialize hp 2 he
  obtain h | h := hp
  · contradiction
  · omega
