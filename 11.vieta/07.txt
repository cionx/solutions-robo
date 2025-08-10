let a := f 0
let g (x : ℤ) := if x ≥ 0 then f x.toNat else a
use g
intro n
simp [g]
