import CollatzProof.Core.Recursion

/-!
# The part of `CollatzProof.Step` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzProof.Step` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzProof.Step` in the source repository.
-/

namespace Collatz

open Classical

/-- The exceptional proportion `e(s) = E(2^s)/2^s`. -/
noncomputable def e (N0 s : ℕ) : ℝ := (E N0 (2 ^ s) : ℝ) / 2 ^ s

lemma e_nonneg (N0 s : ℕ) : 0 ≤ e N0 s := by unfold e; positivity

end Collatz
