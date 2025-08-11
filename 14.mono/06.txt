unfold Injective
intro a₁ a₂ hfa
obtain h | h | h := lt_trichotomy a₁ a₂
· apply hf at h
  omega
· assumption
· apply hf at h
  omega
