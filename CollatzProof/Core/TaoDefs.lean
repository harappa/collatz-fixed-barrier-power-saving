import CollatzProof.Core.Step
import CollatzProof.Core.Syr

/-!
# The part of `CollatzProof.TaoDefs` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzProof.TaoDefs` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzProof.TaoDefs` in the source repository.
-/

namespace Collatz

open Classical

/-- `α = 1.001`. -/
noncomputable def alpha : ℝ := 1.001

/-- The window `2ℕ+1 ∩ [y, y^α]`. -/
noncomputable def W (y : ℝ) : Finset ℕ :=
  (Finset.range (⌊y ^ alpha⌋₊ + 1)).filter (fun N => N % 2 = 1 ∧ y ≤ (N:ℝ))

/-- The logarithmically uniform weight `1/N`. -/
noncomputable def wt (N : ℕ) : ℝ := (N:ℝ)⁻¹

/-- The normalizing sum. -/
noncomputable def Zw (y : ℝ) : ℝ := ∑ N ∈ W y, wt N

/-- `P(P(N_y))`, where `N_y ≡ Log(2ℕ+1 ∩ [y, y^α])`. -/
noncomputable def prob (y : ℝ) (P : ℕ → Prop) : ℝ := (∑ N ∈ (W y).filter P, wt N) / Zw y

/-- `Syr_min(N) > N0`. -/
def SyrMinGT (N0 N : ℕ) : Prop := ∀ k, N0 < Syr^[k] N

/-- `p(y) = P(Syr_min(N_y) > N0)`. -/
noncomputable def p (N0 : ℕ) (y : ℝ) : ℝ := prob y (SyrMinGT N0)

end Collatz
