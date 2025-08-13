unfold Surjective HasRightInverse Function.RightInverse LeftInverse
constructor
· intro h
  choose g hg using h
  use g
· intro ⟨g, hg⟩
  intro b
  use g b
  apply hg b
