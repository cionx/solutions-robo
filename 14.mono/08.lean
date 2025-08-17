unfold Function.RightInverse LeftInverse
unfold LeftInverse at hL
intro x
apply injf
apply hL (f x)
