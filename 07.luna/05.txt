intro ⟨h₃, h₄⟩
intro h₅
simp at h₅
rw [← not_le] at h₅
rw [imp_iff_or_not] at h₅
obtain h₅ | h₅ := h₅
· linarith
· linarith
