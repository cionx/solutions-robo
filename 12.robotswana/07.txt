intro i j hij
trans f (E i j * E j j)
· rw [← congr_arg f (E.mul_same i j j)]
· trans f (E j j * E i j)
  · apply h₁
  · rw [E.mul_of_ne]
    simp
    symm
    assumption
