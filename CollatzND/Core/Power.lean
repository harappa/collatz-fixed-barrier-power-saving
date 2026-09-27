import CollatzND.Core.Col

/-!
# The part of `CollatzND.Power` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzND.Power` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzND.Power` in the source repository.
-/

namespace Collatz

open Classical

/-- Bound the window probability solely by the exceptional proportions on the dyadic shells `ℓ ∈ [a0, a1]` met by the
window (a generalization of `window_to_dyadic`). -/
lemma window_blocks (N0 : ℕ) (y : ℝ) (hy : (2:ℝ) ^ (10000:ℕ) ≤ y) (B : ℝ)
    (hB : ∀ ℓ ∈ Finset.Icc (Nat.log 2 ⌈y⌉₊) (Nat.log 2 ⌊y ^ alpha⌋₊), e N0 (ℓ + 1) ≤ B) :
    p N0 y ≤ 16 * B := by
  have hy1 : (1:ℝ) ≤ y := le_trans (one_le_pow₀ (by norm_num)) hy
  have hgap := dyadic_log_gap hy
  set a0 := Nat.log 2 ⌈y⌉₊
  set a1 := Nat.log 2 ⌊y ^ alpha⌋₊
  have hB0 : 0 ≤ B := le_trans (e_nonneg N0 (a1 + 1)) (hB a1 (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
  have hnum := dyadic_num_le N0 y B hB
  have hden := dyadic_Zw_ge y
  obtain ⟨k, hk⟩ : ∃ k, a1 - a0 - 1 = k := ⟨_, rfl⟩
  have hk2 : 2 ≤ k := by omega
  have hk' : a1 + 1 - a0 = k + 2 := by omega
  rw [hk'] at hnum
  rw [hk] at hden
  push_cast at hnum hden
  have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk2
  have hZ : 0 < Zw y := by linarith
  unfold p prob
  rw [div_le_iff₀ hZ]
  have hkB : 0 ≤ B * ((k:ℝ) - 2) := mul_nonneg hB0 (by linarith)
  calc _ ≤ ((k:ℝ) + 2) * (2 * B) := hnum
    _ ≤ 16 * B * ((k:ℝ) * (1 / 4)) := by nlinarith
    _ ≤ 16 * B * Zw y := by gcongr

/-- General form of the transfer at the top window: if `q = X^{1/α²} ≥ x0`, then the ratio is bounded in terms of
`X^{-1/32000}`, `q^{-1/32000}`, `(log q)^{-1/40}` and the window probability `p(N0, X^{1/α})`. -/
lemma top_general (hM2 : Erdos1135.ND.NDM2Bounds (1 / 32000 : ℝ) (1 / 40)) :
    ∃ Kt x0 : ℝ, 0 ≤ Kt ∧ 2 ≤ x0 ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℝ, 1 ≤ X →
      x0 ≤ Erdos1135.Tao.taoSection3AmbientBoundary X 2 →
        Erdos1135.ND.oddSyracuseBadRatio N0 X ≤
          Kt * (X ^ (-(1 / 32000 : ℝ)) + (Erdos1135.Tao.taoSection3AmbientBoundary X 2) ^ (-(1 / 32000 : ℝ)) +
            (Real.log (Erdos1135.Tao.taoSection3AmbientBoundary X 2)) ^ (-(1 / 40 : ℝ))) +
          2 * p N0 (Erdos1135.Tao.taoSection3AmbientBoundary X 1) := by
  obtain ⟨CHit, CTr, x0, hCHit, hCTr, hx02, hM⟩ := hM2
  refine ⟨2 + 2 * CHit + 2 * CTr, x0, by positivity, hx02, ?_⟩
  intro N0 hN0 X hX1 hqx0
  have hX0 : 0 ≤ X := by linarith
  set y := Erdos1135.Tao.taoSection3AmbientBoundary X 1 with hydef
  set q := Erdos1135.Tao.taoSection3AmbientBoundary X 2 with hqdef
  have hyX : y ^ Erdos1135.Tao.taoAlpha = X := by
    rw [hydef, Erdos1135.Tao.taoSection3AmbientBoundary_succ_rpow hX0 0, boundary_zero]
  have hqy : q ^ Erdos1135.Tao.taoAlpha = y :=
    Erdos1135.Tao.taoSection3AmbientBoundary_succ_rpow hX0 1
  have hq1 : 1 ≤ q := by linarith
  have hyq : q ≤ y := by
    rw [← hqy]
    calc q = q ^ (1:ℝ) := (Real.rpow_one q).symm
      _ ≤ q ^ Erdos1135.Tao.taoAlpha :=
          Real.rpow_le_rpow_of_exponent_le hq1 (by unfold Erdos1135.Tao.taoAlpha; norm_num)
  have hM' := hM q hqx0 hq1 Erdos1135.Tao.TaoSection5SourceBranch.alpha
  simp only at hM'
  obtain ⟨hw, hm, hNH, hL1⟩ := hM'
  have hy'eq : Erdos1135.ND.transportSourceY q Erdos1135.Tao.TaoSection5SourceBranch.alpha = y :=
    hqy
  have hupper : (Erdos1135.ND.transportSourceY q Erdos1135.Tao.TaoSection5SourceBranch.alpha) ^
      Erdos1135.ND.alpha = X := by rw [hy'eq]; exact hyX
  have hy'1 : 1 ≤ Erdos1135.ND.transportSourceY q Erdos1135.Tao.TaoSection5SourceBranch.alpha := by
    rw [hy'eq]; linarith
  have hconv := Erdos1135.ND.oddSyracuseBadRatio_le_ceil_div_add_two_mul_fixedEventTerms
    (b := N0) hN0 hq1 hy'1 hX1 hupper hw hm
  rw [logBad_eq_p] at hconv
  have hceil : (⌈Erdos1135.ND.transportSourceY q Erdos1135.Tao.TaoSection5SourceBranch.alpha⌉₊ : ℝ) / X
      ≤ 2 * X ^ (-(1 / 32000 : ℝ)) := by
    rw [hy'eq]; exact Erdos1135.ND.ceil_taoSection3AmbientBoundary_one_div_le_real_power hX1
  have hpy : p N0 (Erdos1135.ND.transportSourceY q Erdos1135.Tao.TaoSection5SourceBranch.alpha) =
      p N0 y := by rw [hy'eq]
  rw [hpy] at hconv
  simp only [Real.rpow_eq_pow] at hNH hL1
  have hA : (0:ℝ) ≤ X ^ (-(1 / 32000 : ℝ)) := by positivity
  have hB : (0:ℝ) ≤ q ^ (-(1 / 32000 : ℝ)) := by positivity
  have hC : (0:ℝ) ≤ (Real.log q) ^ (-(1 / 40 : ℝ)) := Real.rpow_nonneg (Real.log_nonneg hq1) _
  nlinarith [mul_nonneg hCHit hA, mul_nonneg hCHit hC, mul_nonneg hCTr hA, mul_nonneg hCTr hB]

lemma exp_neg_le_inv (t : ℝ) (ht : 0 < t) : Real.exp (-t) ≤ t⁻¹ := by
  have h := Real.add_one_le_exp t
  rw [Real.exp_neg]
  apply inv_anti₀ ht
  linarith

end Collatz
