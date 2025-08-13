have surj_iff_range_eq_univ {A B} (f : A → B) : Surjective f ↔ range f = univ
· unfold Surjective
  rw [eq_univ_iff_forall]
  simp

constructor
· intro hf
  unfold Injective at hf
  rw [surj_iff_range_eq_univ f]
  apply hf
  ext
  simp
· intro hf
  unfold Injective
  intro A₁ A₂ hA
  apply congr_arg (fun S ↦ f '' S) at hA
  rw [Surjective.image_preimage hf, Surjective.image_preimage hf] at hA
  assumption
