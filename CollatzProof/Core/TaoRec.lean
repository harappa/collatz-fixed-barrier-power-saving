import CollatzProof.Core.TaoDefs

/-!
# The part of `CollatzProof.TaoRec` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzProof.TaoRec` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzProof.TaoRec` in the source repository.
-/

namespace Collatz

open Classical

lemma alpha_gt_one : 1 < alpha := by unfold alpha; norm_num

lemma alpha_pos : 0 < alpha := by unfold alpha; norm_num

lemma rpow_alpha_pow (x1 : ℝ) (hx1 : 0 ≤ x1) (j : ℕ) :
    (x1 ^ (alpha ^ j)) ^ alpha = x1 ^ (alpha ^ (j + 1)) := by
  rw [← Real.rpow_mul hx1, pow_succ]

lemma rpow_alpha_pow2 (x1 : ℝ) (hx1 : 0 ≤ x1) (j : ℕ) :
    (x1 ^ (alpha ^ j)) ^ (alpha ^ 2) = x1 ^ (alpha ^ (j + 2)) := by
  rw [← Real.rpow_mul hx1, pow_add]

lemma le_rpow_alpha_pow (x1 : ℝ) (hx1 : 1 ≤ x1) (j : ℕ) : x1 ≤ x1 ^ (alpha ^ j) := by
  have h1 : (1:ℝ) ≤ alpha ^ j := one_le_pow₀ alpha_gt_one.le
  calc x1 = x1 ^ (1:ℝ) := (Real.rpow_one x1).symm
    _ ≤ x1 ^ (alpha ^ j) := Real.rpow_le_rpow_of_exponent_le hx1 h1

/-- The sum of errors: `Σ_{j<J} (C z_j^{-c} + C log^{-c} z_j) ≤ 2C/(1 - α^{-c}) · log^{-c} x1` (for `x1 > 1`, `C ≥ 0`, `c > 0`). -/
theorem err_sum (C c x1 : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hx1 : 1 < x1) (J : ℕ) :
    ∑ j ∈ Finset.range J, (C * (x1 ^ (alpha ^ j)) ^ (-c) + C * (Real.log (x1 ^ (alpha ^ j))) ^ (-c)) ≤
      2 * C / (1 - alpha ^ (-c)) * (Real.log x1) ^ (-c) := by
  have hlx : 0 < Real.log x1 := Real.log_pos hx1
  have hr0 : 0 < alpha ^ (-c) := Real.rpow_pos_of_pos alpha_pos _
  have hr1 : alpha ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg alpha_gt_one (by linarith)
  have hterm : ∀ j : ℕ, C * (x1 ^ (alpha ^ j)) ^ (-c) + C * (Real.log (x1 ^ (alpha ^ j))) ^ (-c) ≤
      2 * C * (Real.log x1) ^ (-c) * (alpha ^ (-c)) ^ j := by
    intro j
    set z := x1 ^ (alpha ^ j)
    have hz1 : 1 < z := by
      have := le_rpow_alpha_pow x1 hx1.le j; linarith
    have hlogz : Real.log z = alpha ^ j * Real.log x1 := Real.log_rpow (by linarith) _
    have hlz : 0 < Real.log z := Real.log_pos hz1
    have hle : Real.log z ≤ z := by have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < z); linarith
    have h1 : z ^ (-c) ≤ (Real.log z) ^ (-c) := Real.rpow_le_rpow_of_nonpos hlz hle (by linarith)
    have h2 : (Real.log z) ^ (-c) = (Real.log x1) ^ (-c) * (alpha ^ (-c)) ^ j := by
      rw [hlogz, Real.mul_rpow (pow_pos alpha_pos j).le hlx.le, mul_comm]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul alpha_pos.le,
        ← Real.rpow_mul alpha_pos.le, mul_comm]
    calc C * z ^ (-c) + C * (Real.log z) ^ (-c) ≤ C * (Real.log z) ^ (-c) + C * (Real.log z) ^ (-c) := by
          gcongr
      _ = 2 * C * (Real.log x1) ^ (-c) * (alpha ^ (-c)) ^ j := by rw [h2]; ring
  calc _ ≤ ∑ j ∈ Finset.range J, 2 * C * (Real.log x1) ^ (-c) * (alpha ^ (-c)) ^ j :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * C * (Real.log x1) ^ (-c) * ∑ j ∈ Finset.range J, (alpha ^ (-c)) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ 2 * C * (Real.log x1) ^ (-c) * (1 / (1 - alpha ^ (-c))) := by
        gcongr
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0.le hr1
        rw [pow_zero] at this
        rw [Finset.range_eq_Ico]
        exact this
    _ = 2 * C / (1 - alpha ^ (-c)) * (Real.log x1) ^ (-c) := by
        field_simp

/-- The one-step recursion stated as a hypothesis: for `x ≥ X`, `N0 ≥ 1`, `x ≥ N0`, `p(x^{α²}) ≤ p(x^α) + C log^{-c} x`.
It follows both from Tao's Proposition 1.11 (`p_step`) and from the formalization of the recursion of Tao (2022),
Section 3 (`TaoCollatz.descentProb_step`). -/
def StepHyp (C c X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x → ∀ N0 : ℕ, 1 ≤ N0 → (N0:ℝ) ≤ x →
    p N0 (x ^ (alpha ^ 2)) ≤ p N0 (x ^ alpha) + C * (Real.log x) ^ (-c)

/-- Iteration from `StepHyp`. -/
theorem p_iter_step (C c X : ℝ) (hS : StepHyp C c X)
    (N0 : ℕ) (hN0 : 1 ≤ N0) (x1 : ℝ) (hx1 : 1 ≤ x1) (hX : X ≤ x1) (hxN : (N0:ℝ) ≤ x1) :
    ∀ J : ℕ, p N0 (x1 ^ (alpha ^ (J + 1))) ≤ p N0 (x1 ^ alpha) +
      ∑ j ∈ Finset.range J, C * (Real.log (x1 ^ (alpha ^ j))) ^ (-c) := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    have hz := le_rpow_alpha_pow x1 hx1 J
    have hstep := hS (x1 ^ (alpha ^ J)) (le_trans hX hz) N0 hN0 (le_trans hxN hz)
    rw [rpow_alpha_pow x1 (by linarith) J, rpow_alpha_pow2 x1 (by linarith) J] at hstep
    rw [Finset.sum_range_succ]
    linarith

/-- The sum of errors for `StepHyp`. -/
theorem err_sum_step (C c x1 : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hx1 : 1 < x1) (J : ℕ) :
    ∑ j ∈ Finset.range J, C * (Real.log (x1 ^ (alpha ^ j))) ^ (-c) ≤
      2 * C / (1 - alpha ^ (-c)) * (Real.log x1) ^ (-c) := by
  have h := err_sum C c x1 hC hc hx1 J
  have hle : ∀ j ∈ Finset.range J, C * (Real.log (x1 ^ (alpha ^ j))) ^ (-c) ≤
      C * (x1 ^ (alpha ^ j)) ^ (-c) + C * (Real.log (x1 ^ (alpha ^ j))) ^ (-c) := by
    intro j _
    have : 0 ≤ C * (x1 ^ (alpha ^ j)) ^ (-c) := by
      apply mul_nonneg hC
      apply Real.rpow_nonneg
      exact Real.rpow_nonneg (by linarith) _
    linarith
  exact le_trans (Finset.sum_le_sum hle) h

end Collatz
