--div_mul_left is already used by the background library
have div_mul_left2 {a b : ℕ}  : a ∣ a * b
· use b

have div_prod {a : ℕ} {A : Finset ℕ} (h : a ∈ A) : a ∣ ∏ a ∈ A, a
· rw [← insert_erase h]
  rw [prod_insert]
  · apply div_mul_left2
  · simp

let all_primes := hf.toFinset
use ∏ p ∈ all_primes, p
constructor
· apply prod_pos
  intro p hp
  simp [all_primes] at hp
  rw [prime_def] at hp
  omega
· intro p hp
  suffices h : p ∈ all_primes
  · apply div_prod h
  · simp [all_primes]
    assumption
