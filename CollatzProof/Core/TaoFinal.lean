import CollatzProof.Core.TaoRec

/-!
# The part of `CollatzProof.TaoFinal` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzProof.TaoFinal` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzProof.TaoFinal` in the source repository.
-/

namespace Collatz

open Classical

/-- Write the window position `x ≥ X1^α` as `x = x1^{α^{J+1}}` with `X1 ≤ x1 < X1^α`. -/
lemma represent (X1 x : ℝ) (hX1 : 1 < X1) (hx : X1 ^ alpha ≤ x) :
    ∃ J : ℕ, ∃ x1 : ℝ, X1 ≤ x1 ∧ x1 < X1 ^ alpha ∧ x = x1 ^ (alpha ^ (J + 1)) := by
  have hlX : 0 < Real.log X1 := Real.log_pos hX1
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_rpow hX1 alpha_pos) hx
  have hlx : 0 < Real.log x := Real.log_pos hx1
  set r := Real.log x / Real.log X1
  have hr : alpha ≤ r := by
    rw [le_div_iff₀ hlX]
    have := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hx
    rw [Real.log_rpow (by linarith)] at this
    linarith
  have hex : ∃ n : ℕ, r < alpha ^ n := pow_unbounded_of_one_lt r alpha_gt_one
  set n := Nat.find hex
  have hn : r < alpha ^ n := Nat.find_spec hex
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases h : n
    · simp at hn; linarith [alpha_gt_one]
    · simp at hn; linarith
  have hprev : alpha ^ (n - 1) ≤ r := by
    have := Nat.find_min hex (show n - 1 < n by omega)
    push Not at this; exact this
  refine ⟨n - 2, x ^ ((alpha ^ (n - 1))⁻¹), ?_, ?_, ?_⟩
  · -- X1 ≤ x1
    have hp : 0 < alpha ^ (n - 1) := pow_pos alpha_pos _
    rw [← Real.log_le_log_iff (by linarith) (Real.rpow_pos_of_pos (by linarith) _),
      Real.log_rpow (by linarith)]
    rw [le_div_iff₀ hlX] at hprev
    rw [inv_mul_eq_div, le_div_iff₀ hp]; linarith
  · -- x1 < X1^α
    have hp : 0 < alpha ^ (n - 1) := pow_pos alpha_pos _
    rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _),
      Real.log_rpow (by linarith), Real.log_rpow (by linarith)]
    rw [div_lt_iff₀ hlX] at hn
    have e : alpha ^ n = alpha ^ (n - 1) * alpha := by rw [← pow_succ]; congr 1; omega
    rw [e] at hn
    rw [inv_mul_eq_div, div_lt_iff₀ hp]; nlinarith
  · -- x = x1^{α^{J+1}}
    have e : n - 2 + 1 = n - 1 := by omega
    rw [e, ← Real.rpow_mul (by linarith), inv_mul_cancel₀ (pow_pos alpha_pos _).ne', Real.rpow_one]

end Collatz
