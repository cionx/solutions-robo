/- The matrix
 - [ 1 1 ]
 - [ 1 2 ]
 - has determinant 1 is therefore invertible over ℤ,
 - with inverse given by
 - [  2 -1 ]
 - [ -1  1 ] .
 -/

let g := λ ((m, n) : ℤ × ℤ) ↦ (2 * m - n, -m + n)
unfold HasRightInverse
use g
unfold Function.RightInverse Function.LeftInverse
intro (n, m)
simp [f, g]
ring
tauto
