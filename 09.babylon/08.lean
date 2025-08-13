induction n with d hd
. simp
· rw [← insert_Icc_eq_Icc_add_one_right]
  · rw [sum_insert]
    · rw [hd]
      ring
    · simp
  · simp
