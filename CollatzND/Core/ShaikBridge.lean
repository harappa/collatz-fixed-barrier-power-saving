import CollatzND.Core.Uniform
import FirstPassageLinearTransport.FixedBarrier

/-!
# The part of `CollatzND.ShaikBridge` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzND.ShaikBridge` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzND.ShaikBridge` in the source repository.
-/

namespace Collatz

open Classical

lemma T_eq_shortcut : T = FirstPassageLinearTransport.shortcut := by
  funext n; rfl

theorem fixedBarrierHyp_holds : FixedBarrierHyp := by
  obtain ⟨C, c, hC, hc, L0, h⟩ := FirstPassageLinearTransport.FixedBarrier.fixedBarrier_failure_count
  refine ⟨C, c, hC, hc, L0, fun L M hL hLM => ?_⟩
  have h' := h L M hL hLM
  rw [T_eq_shortcut]
  convert h' using 4

/-- **Theorem 1.1 of the paper (Collatz form, unconditional)**: there are `K, c' > 0` such that for all `N0 ≥ 1` and all `X`,
`#{1 ≤ N ≤ X : Col_min(N) > N0} ≤ K N0^{-c'} X` (a power saving uniform in `X`). -/
theorem nd_collatz_uniform :
    ∃ K c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
      (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) ≤
        K * (N0 : ℝ) ^ (-c') * X :=
  nd_collatz_uniform_of_fixedBarrier fixedBarrierHyp_holds

end Collatz
