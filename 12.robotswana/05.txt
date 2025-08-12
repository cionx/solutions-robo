rw [matrix_eq_sum_ebasis 1]
rw [sum_congr rfl]
simp
intro i
trans ∑ j : Fin n, (if i = j then 1 else 0) • E i j
· simp
· rw [sum_congr rfl]
  simp
  intro j
  rw [one_apply]
  simp
