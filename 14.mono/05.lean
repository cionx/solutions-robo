let WeakMono (f : ℤ → ℤ) := ∀ a b : ℤ, a ≤ b → f a ≤ f b

have strict_to_weak (a b : ℤ) : a < b → a ≤ b
· intro h
  omega

have strict_add_weak (f g : ℤ → ℤ) (hf : StrictMono f) (hg : WeakMono g) : StrictMono (f + g)
· unfold StrictMono
  intro a b h₁
  simp
  have h₂ : f a + g a ≤ f a + g b
  · have h : g a ≤ g b := hg a b (strict_to_weak a b h₁)
    omega
  have h₃ : f a + g b < f b + g b
  · have h : f a < f b := hf h₁
    omega
  omega

have const_imp_weak (c : ℤ) : WeakMono (fun x ↦ c)
· simp [WeakMono]

have id_strict : StrictMono (fun (x : ℤ) ↦ x)
· unfold StrictMono
  simp

apply StrictMono.injective
apply StrictMono.add
apply Odd.strictMono_pow
decide
apply strict_add_weak
apply id_strict
apply const_imp_weak
