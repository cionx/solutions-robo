intro 
induction n with d hd
· apply h
· obtain ⟨a, ha⟩ := hd
  use g a
  -- rw [← comp_apply] doesn’t work, so we need more steps
  apply congr_fun at hs
  specialize hs a
  rw [comp_apply, comp_apply] at hs
  rw [hs, ha]
