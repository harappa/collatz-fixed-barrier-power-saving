import CollatzND.Core.ShaikBridge

/-!
# The part of `CollatzND.Explicit` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzND.Explicit` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzND.Explicit` in the source repository.
-/

namespace Collatz

open Classical
open FirstPassageLinearTransport FirstPassageLinearTransport.FixedBarrier

/-- The fixed-barrier rate (explicit). -/
noncomputable def cB : ℝ := min (fbRate / 2) (Real.log 2 / 2)

lemma cB_pos : 0 < cB := by
  unfold cB
  exact lt_min (by have := fbRate_pos; linarith) (by have := Real.log_pos one_lt_two; linarith)

open scoped Classical in
/-- Theorem A (rate `cB` explicit, no time bound, with the factor `L+1`).
A corollary of `FixedBarrier.fixedBarrier_failure_count_rate` (`cB` is definitionally `fbFixedRate`, and `T = shortcut`). -/
theorem fixedBarrier_failure_count_explicit :
    ∃ C : ℝ, 0 < C ∧ ∃ L0 : ℕ, ∀ L M : ℕ, L0 ≤ L → L ≤ M →
      (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n => ∀ k, 2 ^ L ≤ T^[k] n)).card : ℝ)
        ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(cB * L)) := by
  rw [T_eq_shortcut]
  exact fixedBarrier_failure_count_rate

/-- The one-step recursion (exponent `1/40` explicit). -/
theorem stepHyp_nd_explicit : ∃ C X : ℝ, 0 ≤ C ∧ StepHyp C (1 / 40) X := by
  obtain ⟨cg, hPhase⟩ := Erdos1135.ND.existsPhaseGapRhin
  have hd : (0:ℝ) < 1 / 40 := by norm_num
  have hd20 : (1 / 40 : ℝ) < 1 / 20 := by norm_num
  have hdk : (1 / 40 : ℝ) < 1 / (2 * (143 / 10 : ℝ)) := by norm_num
  obtain ⟨B0, -, -, -, -, hBounds⟩ :=
    Erdos1135.ND.exists_ndA5ReferenceSection3SplitRealRatePacket hPhase hd hd20 hdk
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp
    (Erdos1135.ND.eventually_ndA5ReferenceSection3StepError_le_real_log_power B0 hd hd20)
  refine ⟨960084, max X0 ((2:ℝ) ^ (10000:ℕ)), by norm_num, ?_⟩
  intro x hx N0 hN0 _
  have hxX0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hxbig : (2:ℝ) ^ (10000:ℕ) ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1:ℝ) ≤ x := le_trans (one_le_pow₀ (by norm_num)) hxbig
  have hxa : x ≤ x ^ Erdos1135.Tao.taoAlpha := by
    have := le_rpow_alpha_pow x hx1 1
    rwa [pow_one, alpha_eq_tao] at this
  have hxa2 : x ≤ x ^ (Erdos1135.Tao.taoAlpha ^ 2) := by
    have := le_rpow_alpha_pow x hx1 2
    rwa [alpha_eq_tao] at this
  have hm1 := mass_pos (x ^ Erdos1135.Tao.taoAlpha) (le_trans hxbig hxa)
  have hm2 := mass_pos (x ^ (Erdos1135.Tao.taoAlpha ^ 2)) (le_trans hxbig hxa2)
  obtain ⟨-, hNH2, hTV⟩ := hBounds x _ _ _ _ hx1 ⟨rfl, rfl, rfl, rfl⟩ hm1 hm2
  simp only [Erdos1135.Tao.taoProp111RealY1, Erdos1135.Tao.taoProp111RealY2] at hNH2 hTV
  have hstep := Erdos1135.Tao.taoSection3_fixedTargetGood_real_oneStep (b := N0) hN0 hx1 hm1 hm2
  rw [good_eq_one_sub_p N0 _ hm1, good_eq_one_sub_p N0 _ hm2] at hstep
  have herr := hX0 x hxX0
  unfold Erdos1135.Tao.taoSection3AmbientStepError at herr
  rw [alpha_eq_tao]
  linarith


/-- Assembly (takes the rate `c` and the recursion exponent `cs` as arguments and returns `K > 0`). -/
theorem nd_syracuse_uniform_explicit_of (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (L0 : ℕ)
    (hB : ∀ L M : ℕ, L0 ≤ L → L ≤ M →
      (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (fun n => ∀ k, 2 ^ L ≤ T^[k] n)).card : ℝ)
        ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)))
    (Cs cs Xs : ℝ) (hCs : 0 ≤ Cs) (hcs : 0 < cs) (hStep : StepHyp Cs cs Xs) :
    ∃ K : ℝ, 0 < K ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℝ, 2 ≤ X →
      Erdos1135.ND.oddSyracuseBadRatio N0 X ≤
        K * (N0 : ℝ) ^ (-(c * min (1 / 80) (cs / 2) / (2 * Real.log 2))) := by
  obtain ⟨hM2, -⟩ := Erdos1135.ND.ndRhinRate_sameD (1 / 40) (by norm_num) (by norm_num)
  obtain ⟨Kt, x0, hKt, hx02, htop⟩ := top_general hM2
  have ha := alpha_pos
  have ha1 := alpha_gt_one
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  set K1 : ℝ := 2 * Cs / (1 - alpha ^ (-cs)) with hK1def
  have hK1 : 0 ≤ K1 := by
    have : alpha ^ (-cs) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha1 (by linarith)
    apply div_nonneg (by linarith) (by linarith)
  set c1 : ℝ := c * min (1 / 80) (cs / 2) with hc1def
  have hc1 : 0 < c1 := mul_pos hc (lt_min (by norm_num) (by linarith))
  set c' : ℝ := c1 / (2 * Real.log 2) with hc'def
  have hc' : 0 < c' := by positivity
  set Mth : ℝ := max (max ((2:ℝ) ^ (10000:ℕ)) Xs) (max x0 1) with hMth
  have hMth1 : 1 ≤ Mth := le_trans (le_max_right _ _) (le_max_right _ _)
  set Lstar : ℕ := max L0 (max ⌈16 / c ^ 2⌉₊ ⌈2 * Mth / c⌉₊) + 1 with hLstar
  set K3 : ℝ := Kt * 64001 + 2 * (16 * C * (alpha ^ 3 / Real.log 2 + 2) + K1) +
    2 * C * (alpha ^ 2 / Real.log 2 + 1) with hK3
  have hK3nn : 0 ≤ K3 := by positivity
  set Kbig : ℝ := K3 * ((1 + 2 / c1) * Real.exp (c1 / 2)) with hKbig
  set K : ℝ := max Kbig (2 * ((2:ℝ) ^ Lstar) ^ c') with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨K, hKpos, ?_⟩
  intro N0 hN0 X hX
  have hN0pos : (0:ℝ) < N0 := by exact_mod_cast (by omega : 0 < N0)
  have hNpow : 0 < (N0:ℝ) ^ (-c') := Real.rpow_pos_of_pos hN0pos _
  set L := Nat.log 2 N0 with hLdef
  by_cases hsmall : L < Lstar
  · -- `N0 < 2^{Lstar}`: ratio ≤ 2
    have hr := Erdos1135.ND.oddSyracuseBadRatio_le_two N0 (by linarith : (1:ℝ) ≤ X)
    have hN0lt : (N0:ℝ) ≤ (2:ℝ) ^ Lstar := by
      have h1 : N0 < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N0
      have h2 : 2 ^ (L + 1) ≤ 2 ^ Lstar := Nat.pow_le_pow_right (by norm_num) hsmall
      exact_mod_cast (le_trans h1.le h2)
    have h1 : (N0:ℝ) ^ c' ≤ ((2:ℝ) ^ Lstar) ^ c' := Real.rpow_le_rpow hN0pos.le hN0lt hc'.le
    have h2 : (N0:ℝ) ^ c' * (N0:ℝ) ^ (-c') = 1 := by rw [← Real.rpow_add hN0pos]; simp
    calc Erdos1135.ND.oddSyracuseBadRatio N0 X ≤ 2 := hr
      _ = 2 * ((N0:ℝ) ^ c' * (N0:ℝ) ^ (-c')) := by rw [h2]; ring
      _ ≤ 2 * (((2:ℝ) ^ Lstar) ^ c' * (N0:ℝ) ^ (-c')) := by gcongr
      _ = (2 * ((2:ℝ) ^ Lstar) ^ c') * (N0:ℝ) ^ (-c') := by ring
      _ ≤ K * (N0:ℝ) ^ (-c') := by gcongr; exact le_max_right _ _
  · push Not at hsmall
    have hLr : (Lstar : ℝ) ≤ L := by exact_mod_cast hsmall
    have hL0 : L0 ≤ L := le_trans (le_trans (le_max_left _ _) (Nat.le_succ _)) hsmall
    have hL1 : (1:ℝ) ≤ L := by
      have : 1 ≤ Lstar := Nat.succ_pos _
      exact_mod_cast le_trans this hsmall
    have hLc : 16 / c ^ 2 ≤ (L:ℝ) := by
      have h1 : (⌈16 / c ^ 2⌉₊ : ℝ) ≤ Lstar := by
        have : ⌈16 / c ^ 2⌉₊ ≤ Lstar :=
          le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (Nat.le_succ _)
        exact_mod_cast this
      linarith [Nat.le_ceil (16 / c ^ 2)]
    have hLM : 2 * Mth / c ≤ (L:ℝ) := by
      have h1 : (⌈2 * Mth / c⌉₊ : ℝ) ≤ Lstar := by
        have : ⌈2 * Mth / c⌉₊ ≤ Lstar :=
          le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (Nat.le_succ _)
        exact_mod_cast this
      linarith [Nat.le_ceil (2 * Mth / c)]
    set v : ℝ := Real.exp (c * L / 2) with hvdef
    have hv1 : 1 ≤ v := Real.one_le_exp (by positivity)
    have hv0 : 0 < v := by linarith
    -- `v ≥ Mth`
    have hvM : Mth ≤ v := by
      have := Real.add_one_le_exp (c * L / 2)
      have : Mth ≤ c * L / 2 := by
        rw [div_le_iff₀ hc] at hLM; linarith
      linarith
    have hevM : Mth ≤ Real.exp v := le_trans hvM (by have := Real.add_one_le_exp v; linarith)
    have hbig : (2:ℝ) ^ (10000:ℕ) ≤ Real.exp v := le_trans (by simp [hMth]) hevM
    have hXse : Xs ≤ Real.exp v := le_trans (by simp [hMth]) hevM
    have hx0e : x0 ≤ Real.exp v := le_trans (by simp [hMth]) hevM
    -- `N0 ≤ e^v`
    have hN0v : (N0:ℝ) ≤ Real.exp v := by
      have hN0lt : (N0:ℝ) < 2 ^ (L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N0
      have hq : (c * L / 2) ^ 2 / 2 ≤ v := by
        have := Real.pow_div_factorial_le_exp (x := c * L / 2) (by positivity) 2
        simpa using this
      have hq2 : ((L:ℝ) + 1) * Real.log 2 ≤ (c * L / 2) ^ 2 / 2 := by
        have h1 : 16 ≤ c ^ 2 * L := by rw [div_le_iff₀ (by positivity)] at hLc; linarith
        nlinarith
      have h2 : (2:ℝ) ^ (L + 1) = Real.exp (((L:ℝ) + 1) * Real.log 2) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]; push_cast; ring_nf
      rw [h2] at hN0lt
      exact le_trans hN0lt.le (Real.exp_le_exp.mpr (le_trans hq2 hq))
    have hwin := window_uniform C c hC L0 hB Cs cs Xs hCs hcs hStep N0 hN0 hL0 v hv0 hbig hXse hN0v
    obtain ⟨fa, fb, fc, fd, fe⟩ := v_facts c cs L v c1 hc hcs (Nat.cast_nonneg L) hvdef hc1def
    have hLp1 : (1:ℝ) ≤ (L:ℝ) + 1 := by linarith
    have hE1 : 0 ≤ Real.exp (-(c1 * L)) := (Real.exp_pos _).le
    have hgoal : Erdos1135.ND.oddSyracuseBadRatio N0 X ≤ K3 * (((L:ℝ) + 1) * Real.exp (-(c1 * L))) := by
      by_cases hXs : X < (Real.exp v) ^ (alpha ^ 2)
      · have h := small_uniform C c hC L0 hB N0 hN0 hL0 v hv0 X hX hXs
        rw [show alpha ^ 2 * v / Real.log 2 = alpha ^ 2 / Real.log 2 * v by ring] at h
        have h' := arith_small _ C (alpha ^ 2 / Real.log 2) v _ _ (L:ℝ) hC.le (by positivity)
          (by linarith) h fa fb
        refine le_trans h' (mul_le_mul_of_nonneg_right ?_ (by positivity))
        rw [hK3]
        have : 0 ≤ Kt * 64001 + 2 * (16 * C * (alpha ^ 3 / Real.log 2 + 2) + K1) := by positivity
        linarith
      · push Not at hXs
        have h := top_generic Kt x0 _ v N0 hKt hv1 hx0e (htop N0 hN0) hwin X hXs
        rw [show alpha ^ 3 * v / Real.log 2 = alpha ^ 3 / Real.log 2 * v by ring, ← hK1def] at h
        have h' := arith_large _ Kt C (alpha ^ 3 / Real.log 2) K1 v v⁻¹ _ _ _ _ (L:ℝ) hKt hC.le
          (by positivity) hK1 hLp1 hE1 h fa fb fc fd fe
        refine le_trans h' (mul_le_mul_of_nonneg_right ?_ (by positivity))
        rw [hK3]
        have : 0 ≤ 2 * C * (alpha ^ 2 / Real.log 2 + 1) := by positivity
        linarith
    have hrate := rate_to_N0 c1 hc1 N0 hN0
    calc Erdos1135.ND.oddSyracuseBadRatio N0 X ≤ K3 * (((L:ℝ) + 1) * Real.exp (-(c1 * L))) := hgoal
      _ ≤ K3 * ((1 + 2 / c1) * Real.exp (c1 / 2) * (N0 : ℝ) ^ (-c')) := by
          apply mul_le_mul_of_nonneg_left _ hK3nn; exact hrate
      _ = Kbig * (N0 : ℝ) ^ (-c') := by rw [hKbig]; ring
      _ ≤ K * (N0 : ℝ) ^ (-c') := by gcongr; exact le_max_left _ _


/-- The exponent `c'` of Theorem 1.1 of the paper (explicit). -/
noncomputable def tstarExponent : ℝ := cB * min (1 / 80) ((1 / 40 : ℝ) / 2) / (2 * Real.log 2)

lemma tstarExponent_eq : tstarExponent = cB / (160 * Real.log 2) := by
  unfold tstarExponent
  have hm : min (1 / 80 : ℝ) ((1 / 40 : ℝ) / 2) = 1 / 80 := by norm_num
  rw [hm]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  field_simp
  ring

lemma tstarExponent_pos : 0 < tstarExponent := by
  rw [tstarExponent_eq]
  have := cB_pos
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  positivity

/-- **Syracuse form of Theorem 1.1 of the paper (the bound on `ρ(N0, X)` in Section 6; explicit exponent, `K > 0`)**. -/
theorem nd_syracuse_uniform_explicit :
    ∃ K : ℝ, 0 < K ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℝ, 2 ≤ X →
      Erdos1135.ND.oddSyracuseBadRatio N0 X ≤ K * (N0 : ℝ) ^ (-tstarExponent) := by
  obtain ⟨C, hC, L0, hB⟩ := fixedBarrier_failure_count_explicit
  obtain ⟨Cs, Xs, hCs, hStep⟩ := stepHyp_nd_explicit
  obtain ⟨K, hK, h⟩ := nd_syracuse_uniform_explicit_of C cB hC cB_pos L0 hB Cs (1 / 40) Xs hCs
    (by norm_num) hStep
  exact ⟨K, hK, h⟩

/-- **Theorem 1.1 of the paper (Collatz form, explicit exponent, `K > 0`)**: for all `N0 ≥ 1` and `X`,
`#{1 ≤ N ≤ X : Col_min(N) > N0} ≤ K N0^{-tstarExponent} X`, `tstarExponent = cB/(160 log 2)`. -/
theorem nd_collatz_uniform_explicit :
    ∃ K : ℝ, 0 < K ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
      (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) ≤
        K * (N0 : ℝ) ^ (-tstarExponent) * X := by
  obtain ⟨K, hK, h⟩ := nd_syracuse_uniform_explicit
  refine ⟨2 * K, by positivity, ?_⟩
  intro N0 hN0 X
  set ε := K * (N0 : ℝ) ^ (-tstarExponent) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hO : ∀ Y : ℕ, (Erdos1135.ND.natCountLE (Erdos1135.ND.oddSyracuseBadSet N0) Y : ℝ) ≤ ε * Y := by
    intro Y
    rcases Nat.lt_or_ge Y 2 with hY | hY
    · rw [natCountLE_small N0 Y hN0 (by omega)]; simp; positivity
    · have hYr : (2:ℝ) ≤ Y := by exact_mod_cast hY
      have hr := h N0 hN0 Y hYr
      unfold Erdos1135.ND.oddSyracuseBadRatio Erdos1135.ND.natCountLEReal at hr
      rw [Nat.floor_natCast, div_le_iff₀ (by linarith)] at hr
      exact hr
  have hA := A_bound N0 ε hε0 hO X
  have hEq : (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) = (A N0 X : ℝ) :=
    rfl
  rw [hEq]
  calc (A N0 X : ℝ) ≤ 2 * ε * X := hA
    _ = 2 * K * (N0 : ℝ) ^ (-tstarExponent) * X := by rw [hε]; ring

end Collatz
