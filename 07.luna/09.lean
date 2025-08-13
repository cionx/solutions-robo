use (a + c) / 2
obtain hac | hac | hac := lt_trichotomy a c
· left
  constructor
  · linarith
  · linarith
· contradiction
· right
  constructor
  · linarith
  · linarith
