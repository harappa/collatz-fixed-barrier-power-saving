import CollatzProof.Core.TaoDefs

/-!
# The part of `CollatzProof.Conv` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzProof.Conv` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzProof.Conv` in the source repository.
-/

namespace Collatz

open Classical

/-- If `y ≥ 2^{10000}` then `16 y ≤ y^α` (since `y^{0.001} ≥ 2^{10}`). -/
lemma dyadic_sixteen_mul_le_rpow_alpha {y : ℝ} (hy : (2:ℝ) ^ (10000:ℕ) ≤ y) : 16 * y ≤ y ^ alpha := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have h1 : y ^ alpha = y * y ^ (0.001:ℝ) := by
    rw [show alpha = 1 + 0.001 by unfold alpha; norm_num, Real.rpow_add hy0, Real.rpow_one]
  have h2 : ((2:ℝ) ^ (10000:ℕ)) ^ (0.001:ℝ) ≤ y ^ (0.001:ℝ) :=
    Real.rpow_le_rpow (by positivity) hy (by norm_num)
  have h3 : ((2:ℝ) ^ (10000:ℕ)) ^ (0.001:ℝ) = 2 ^ (10:ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    norm_num
  rw [h3] at h2
  have h4 : (16:ℝ) ≤ y ^ (0.001:ℝ) := le_trans (by norm_num) h2
  rw [h1, mul_comm 16 y]
  exact mul_le_mul_of_nonneg_left h4 hy0.le

/-- The binary logarithm of the upper end of the window: `Nat.log 2 ⌊y^α⌋₊ ≤ α log₂ y`. -/
lemma dyadic_log_floor_le {y : ℝ} (hy0 : 0 < y) (h : ⌊y ^ alpha⌋₊ ≠ 0) :
    (Nat.log 2 ⌊y ^ alpha⌋₊ : ℝ) ≤ alpha * Real.logb 2 y := by
  have hY : 0 < y ^ alpha := Real.rpow_pos_of_pos hy0 _
  rw [← Real.logb_rpow_eq_mul_logb_of_pos hy0, Real.le_logb_iff_rpow_le (by norm_num) hY,
    Real.rpow_natCast]
  have h1 := Nat.pow_log_le_self 2 h
  have h2 := Nat.floor_le hY.le
  calc (2:ℝ) ^ Nat.log 2 ⌊y ^ alpha⌋₊ = ((2 ^ Nat.log 2 ⌊y ^ alpha⌋₊ : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (⌊y ^ alpha⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ y ^ alpha := h2

/-- Restatement of membership in the window `W y`. -/
lemma dyadic_mem_W {y : ℝ} {N : ℕ} : N ∈ W y ↔ N ≤ ⌊y ^ alpha⌋₊ ∧ N % 2 = 1 ∧ y ≤ (N:ℝ) := by
  unfold W
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- Numerator: on each dyadic interval meeting the window, bound the sum from above by the exceptional proportion. -/
lemma dyadic_num_le (N0 : ℕ) (y : ℝ) (B : ℝ)
    (hB : ∀ ℓ ∈ Finset.Icc (Nat.log 2 ⌈y⌉₊) (Nat.log 2 ⌊y ^ alpha⌋₊), e N0 (ℓ + 1) ≤ B) :
    ∑ N ∈ (W y).filter (SyrMinGT N0), wt N ≤
      ((Nat.log 2 ⌊y ^ alpha⌋₊ + 1 - Nat.log 2 ⌈y⌉₊ : ℕ) : ℝ) * (2 * B) := by
  set a0 := Nat.log 2 ⌈y⌉₊
  set a1 := Nat.log 2 ⌊y ^ alpha⌋₊
  set S := (W y).filter (SyrMinGT N0)
  have hmaps : ∀ N ∈ S, Nat.log 2 N ∈ Finset.Icc a0 a1 := by
    intro N hN
    simp only [S, Finset.mem_filter, dyadic_mem_W] at hN
    obtain ⟨⟨hNu, _, hyN⟩, _⟩ := hN
    have hc : ⌈y⌉₊ ≤ N := Nat.ceil_le.mpr hyN
    exact Finset.mem_Icc.mpr ⟨Nat.log_mono_right hc, Nat.log_mono_right hNu⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ ℓ ∈ Finset.Icc a0 a1,
      ∑ N ∈ S.filter (fun N => Nat.log 2 N = ℓ), wt N ≤ 2 * B := by
    intro ℓ hℓ
    have h1 : ∑ N ∈ S.filter (fun N => Nat.log 2 N = ℓ), wt N ≤
        ∑ N ∈ S.filter (fun N => Nat.log 2 N = ℓ), ((2:ℝ) ^ ℓ)⁻¹ := by
      apply Finset.sum_le_sum
      intro N hN
      simp only [S, Finset.mem_filter, dyadic_mem_W] at hN
      obtain ⟨⟨⟨_, hodd, _⟩, _⟩, hlog⟩ := hN
      have hN0 : N ≠ 0 := by omega
      have hp : 2 ^ ℓ ≤ N := hlog ▸ Nat.pow_log_le_self 2 hN0
      unfold wt
      apply inv_anti₀ (by positivity)
      exact_mod_cast hp
    have h2 : (S.filter (fun N => Nat.log 2 N = ℓ)).card ≤ E N0 (2 ^ (ℓ + 1)) := by
      unfold E
      apply Finset.card_le_card
      intro N hN
      simp only [S, Finset.mem_filter, dyadic_mem_W] at hN
      obtain ⟨⟨⟨_, hodd, _⟩, hsyr⟩, hlog⟩ := hN
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, exc_of_syr hodd hsyr⟩
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
      rw [hlog] at this
      exact this
    have h3 := hB ℓ hℓ
    unfold e at h3
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h4 : ((S.filter (fun N => Nat.log 2 N = ℓ)).card : ℝ) ≤ (E N0 (2 ^ (ℓ + 1)) : ℝ) := by
      exact_mod_cast h2
    have h5 : (E N0 (2 ^ (ℓ + 1)) : ℝ) * ((2:ℝ) ^ ℓ)⁻¹ = 2 * ((E N0 (2 ^ (ℓ + 1)) : ℝ) / 2 ^ (ℓ + 1)) := by
      rw [pow_succ (2:ℝ) ℓ]; field_simp
    calc _ ≤ _ := h1
      _ ≤ (E N0 (2 ^ (ℓ + 1)) : ℝ) * ((2:ℝ) ^ ℓ)⁻¹ := by gcongr
      _ = _ := h5
      _ ≤ 2 * B := by linarith
  calc _ ≤ ∑ ℓ ∈ Finset.Icc a0 a1, 2 * B := Finset.sum_le_sum hblock
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]

/-- Denominator: for a dyadic interval `[2^ℓ, 2^{ℓ+1})` contained in the window, the sum of the weights of its odd numbers is at least `1/4`. -/
lemma dyadic_block_ge (y : ℝ) (ℓ : ℕ)
    (hℓ : ℓ ∈ Finset.Ioo (Nat.log 2 ⌈y⌉₊) (Nat.log 2 ⌊y ^ alpha⌋₊)) :
    (1:ℝ) / 4 ≤ ∑ N ∈ ((W y).filter (fun N => Nat.log 2 N ∈
      Finset.Ioo (Nat.log 2 ⌈y⌉₊) (Nat.log 2 ⌊y ^ alpha⌋₊))).filter (fun N => Nat.log 2 N = ℓ),
      wt N := by
  set a0 := Nat.log 2 ⌈y⌉₊
  set a1 := Nat.log 2 ⌊y ^ alpha⌋₊
  have hℓ' := Finset.mem_Ioo.mp hℓ
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hu : ⌊y ^ alpha⌋₊ ≠ 0 := by
    intro h0
    have : a1 = 0 := by simp only [a1, h0, Nat.log_zero_right]
    omega
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have hpow2 : 2 ^ (m + 1 + 1) = 4 * 2 ^ m := by rw [pow_succ, pow_succ]; ring
  set img := (Finset.range (2 ^ m)).image (fun i => 2 ^ (m + 1) + 2 * i + 1)
  have hsub : img ⊆ ((W y).filter (fun N => Nat.log 2 N ∈ Finset.Ioo a0 a1)).filter
      (fun N => Nat.log 2 N = m + 1) := by
    intro N hN
    simp only [img, Finset.mem_image, Finset.mem_range] at hN
    obtain ⟨i, hi, rfl⟩ := hN
    have hlo : 2 ^ (m + 1) ≤ 2 ^ (m + 1) + 2 * i + 1 := by omega
    have hhi : 2 ^ (m + 1) + 2 * i + 1 < 2 ^ (m + 1 + 1) := by omega
    have hlog : Nat.log 2 (2 ^ (m + 1) + 2 * i + 1) = m + 1 := Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
    simp only [Finset.mem_filter, dyadic_mem_W, hlog]
    refine ⟨⟨⟨?_, by omega, ?_⟩, hℓ⟩, trivial⟩
    · have h1 : 2 ^ (m + 1 + 1) ≤ 2 ^ a1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ a1 ≤ ⌊y ^ alpha⌋₊ := Nat.pow_log_le_self 2 hu
      omega
    · have h1 : ⌈y⌉₊ < 2 ^ (a0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : 2 ^ (a0 + 1) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : ⌈y⌉₊ ≤ 2 ^ (m + 1) + 2 * i + 1 := by omega
      calc y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
        _ ≤ _ := by exact_mod_cast h3
  have hwt : ∀ N ∈ img, ((2:ℝ) ^ (m + 1 + 1))⁻¹ ≤ wt N := by
    intro N hN
    simp only [img, Finset.mem_image, Finset.mem_range] at hN
    obtain ⟨i, hi, rfl⟩ := hN
    have hhi : 2 ^ (m + 1) + 2 * i + 1 ≤ 2 ^ (m + 1 + 1) := by omega
    unfold wt
    apply inv_anti₀ (by positivity)
    exact_mod_cast hhi
  have hcard : img.card = 2 ^ m := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  calc (1:ℝ) / 4 = ∑ N ∈ img, ((2:ℝ) ^ (m + 1 + 1))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        push_cast
        rw [pow_succ, pow_succ]
        field_simp
        ring
    _ ≤ ∑ N ∈ img, wt N := Finset.sum_le_sum hwt
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun N _ _ => by unfold wt; positivity)

/-- Lower bound for the denominator: `Zw y ≥ (number of intervals entirely contained in the window)/4`. -/
lemma dyadic_Zw_ge (y : ℝ) :
    ((Nat.log 2 ⌊y ^ alpha⌋₊ - Nat.log 2 ⌈y⌉₊ - 1 : ℕ) : ℝ) * (1 / 4) ≤ Zw y := by
  set a0 := Nat.log 2 ⌈y⌉₊
  set a1 := Nat.log 2 ⌊y ^ alpha⌋₊
  set F := (W y).filter (fun N => Nat.log 2 N ∈ Finset.Ioo a0 a1)
  have hmaps : ∀ N ∈ F, Nat.log 2 N ∈ Finset.Ioo a0 a1 := by
    intro N hN
    exact (Finset.mem_filter.mp hN).2
  calc ((a1 - a0 - 1 : ℕ) : ℝ) * (1 / 4) = ∑ ℓ ∈ Finset.Ioo a0 a1, (1:ℝ) / 4 := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioo]
    _ ≤ ∑ ℓ ∈ Finset.Ioo a0 a1, ∑ N ∈ F.filter (fun N => Nat.log 2 N = ℓ), wt N :=
        Finset.sum_le_sum (fun ℓ hℓ => dyadic_block_ge y ℓ hℓ)
    _ = ∑ N ∈ F, wt N := Finset.sum_fiberwise_of_maps_to hmaps _
    _ ≤ ∑ N ∈ W y, wt N :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun N _ _ => by unfold wt; positivity)
    _ = Zw y := rfl

/-- Width of the window: if `y ≥ 2^{10000}`, then `2^{a0+3} ≤ ⌊y^α⌋₊`, i.e. `a0 + 3 ≤ a1`. -/
lemma dyadic_log_gap {y : ℝ} (hy : (2:ℝ) ^ (10000:ℕ) ≤ y) :
    Nat.log 2 ⌈y⌉₊ + 3 ≤ Nat.log 2 ⌊y ^ alpha⌋₊ := by
  have hy1 : (1:ℝ) ≤ y := le_trans (one_le_pow₀ (by norm_num)) hy
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hc : ⌈y⌉₊ ≠ 0 := (Nat.ceil_pos.mpr hy0).ne'
  have h1 : 2 ^ Nat.log 2 ⌈y⌉₊ ≤ ⌈y⌉₊ := Nat.pow_log_le_self 2 hc
  have h2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
  have h3 := dyadic_sixteen_mul_le_rpow_alpha hy
  apply Nat.le_log_of_pow_le (by norm_num)
  apply Nat.le_floor
  have h1' : ((2 ^ Nat.log 2 ⌈y⌉₊ : ℕ) : ℝ) ≤ (⌈y⌉₊ : ℝ) := by exact_mod_cast h1
  push_cast at h1' ⊢
  rw [pow_add, show (2:ℝ) ^ 3 = 8 by norm_num]
  clear hy
  linarith

end Collatz
