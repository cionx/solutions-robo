constructor
· intro h
  by_cases hA : A
  · right
    apply h
    assumption
  · left
    assumption
· intro h
  · obtain hnA | hb := h
    · intro hA
      contradiction
    · intro hA
      assumption
