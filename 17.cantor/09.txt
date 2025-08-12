intro s
-- We consider the set
--   T = { a' ∈ A | a' ∉ f a' }
--     = { a' ∈ A | ¬ a' ∈ f a' }
--     = { a' ∈ A | ¬ f a' a' } .
-- This is a subset of A depending on the function f : A → Sets A.
-- Assuming that f were surjective, there would now exists
-- some a : A with f a = T. This a ought to be the desired
-- fixed point, as discussed in the solution to the previous level.

let T := fun a' ↦ s (f a' a')
obtain ⟨a, ha⟩ := hf T
-- f a a is the truth value of a ∈ {a' ∈ A' | ¬ f a' a'}.
-- This will then be a fixed point to ¬, which for negation gives a contradiction.
use f a a
simp
unfold IsFixedPt
nth_rw 2 [ha]
