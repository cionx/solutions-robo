ext b
simp
constructor
· intro ⟨a, ha1, ha2⟩
  rw [← ha2]
  assumption
· intro hb
  obtain ⟨a, ha⟩ := hf b
  use a
  constructor
  · rw [ha]
    assumption
  · assumption
