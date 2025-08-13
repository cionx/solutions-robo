/-
Idea.
A function f : A → Set A corresponds to a function f : A → A → Ω for Ω = {⊤, ⊥}.
We also have the negation function ¬ : Ω → Ω.
We have
  a ∈ f b   iff   f a b = ⊤
and thus
  a ∉ f a   iff   ¬ (f a a) = ⊥ .

So, in the proof of Cantor’s diagonal argument we assume an a : A with
  f a = {a' ∈ A | a' ∉ f a'} .
and thus
  f a = (a' ↦ ¬ f a' a').

We then conclude that
  a ∈ f a   iff   a ∉ f a ,
or in other word
  f a a  =  ¬ f a a .
This means precisely that f a a is a fixed point for ¬.
-/

unfold IsFixedPt
nth_rw 2 [ha]
