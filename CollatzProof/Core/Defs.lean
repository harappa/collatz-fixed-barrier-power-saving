import Mathlib

/-!
# The part of `CollatzProof.Defs` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzProof.Defs` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzProof.Defs` in the source repository.
-/

namespace Collatz

/-- The shortcut map: `T(n) = n/2` (`n` even), `(3n+1)/2` (`n` odd). -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

lemma two_mul_T_of_odd {m : ℕ} (h : m % 2 = 1) : 2 * T m = 3 * m + 1 := by
  unfold T; split_ifs <;> omega

lemma two_mul_T_of_even {m : ℕ} (h : m % 2 = 0) : 2 * T m = m := by
  unfold T; split_ifs <;> omega

end Collatz
