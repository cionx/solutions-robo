intro h hx
unfold Even at hx
unfold Odd
obtain ⟨r, hr⟩ := hx
use r
rw [hr]
ring
