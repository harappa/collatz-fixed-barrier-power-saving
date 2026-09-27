import CollatzND.Core.Power

/-!
# The part of `CollatzND.Uniform` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzND.Uniform` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzND.Uniform` in the source repository.
-/

namespace Collatz

open Classical

/-- The fixed-target form of Theorem 5.3 of Shaik's manuscript (a hypothesis here; it is discharged in
`ShaikBridge.lean` by `fixedBarrier_failure_count`, which this project assembled from lemmas of Shaik's formalization). -/
def FixedBarrierHyp : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ L0 : ℕ, ∀ L M : ℕ, L0 ≤ L → L ≤ M →
    (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (fun n => ∀ k, 2 ^ L ≤ T^[k] n)).card : ℝ)
      ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L))

/-- The number of exceptions per dyadic shell. -/
lemma shell_exc_le (C c : ℝ) (hC : 0 < C) (L0 : ℕ)
    (hB : ∀ L M : ℕ, L0 ≤ L → L ≤ M →
      (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (fun n => ∀ k, 2 ^ L ≤ T^[k] n)).card : ℝ)
        ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)))
    (N0 : ℕ) (hN0 : 1 ≤ N0) (hL : L0 ≤ Nat.log 2 N0) (M : ℕ) :
    (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (Exc N0)).card : ℝ)
      ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := by
  set L := Nat.log 2 N0 with hLdef
  have hpowL : 2 ^ L ≤ N0 := Nat.pow_log_le_self 2 (by omega)
  by_cases hML : L ≤ M
  · refine le_trans ?_ (hB L M hL hML)
    have hsub : (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (Exc N0) ⊆
        (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (fun n => ∀ k, 2 ^ L ≤ T^[k] n) := by
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, fun k => le_trans hpowL (hn.2 k).le⟩
    exact_mod_cast Finset.card_le_card hsub
  · push Not at hML
    have hzero : (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (Exc N0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n hn hexc
      rw [Finset.mem_Ico] at hn
      have h1 : 2 ^ (M + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hML
      have := hexc 0
      simp only [Function.iterate_zero, id] at this
      omega
    rw [hzero]; simp only [Finset.card_empty, Nat.cast_zero]; positivity

/-- The exceptional proportion on the dyadic interval `[0, 2^M)`: `e(N0, M) ≤ C·M·(L+1)·e^{-cL}`. -/
lemma e_fixed (C c : ℝ) (hC : 0 < C) (L0 : ℕ)
    (hB : ∀ L M : ℕ, L0 ≤ L → L ≤ M →
      (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (fun n => ∀ k, 2 ^ L ≤ T^[k] n)).card : ℝ)
        ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)))
    (N0 : ℕ) (hN0 : 1 ≤ N0) (hL : L0 ≤ Nat.log 2 N0) (M : ℕ) :
    e N0 M ≤ C * (M : ℝ) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := by
  set L := Nat.log 2 N0 with hLdef
  set D : ℝ := C * ((L : ℝ) + 1) * Real.exp (-(c * L)) with hD
  have hD0 : 0 ≤ D := by positivity
  have key : ∀ M : ℕ, (E N0 (2 ^ M) : ℝ) ≤ D * M * 2 ^ M := by
    intro M
    induction M with
    | zero =>
      have : E N0 1 = 0 := by
        unfold E
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro n hn hexc
        rw [Finset.mem_range] at hn
        have := hexc 0
        simp only [Function.iterate_zero, id] at this
        omega
      simp [this]
    | succ M ih =>
      have hsplit : E N0 (2 ^ (M + 1)) ≤ E N0 (2 ^ M) +
          ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (Exc N0)).card := by
        unfold E
        have hr : Finset.range (2 ^ (M + 1)) = Finset.range (2 ^ M) ∪ Finset.Ico (2 ^ M) (2 ^ (M + 1)) := by
          rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _)
            (Nat.pow_le_pow_right (by norm_num) (by omega))]
        rw [hr, Finset.filter_union]
        exact Finset.card_union_le _ _
      have hshell := shell_exc_le C c hC L0 hB N0 hN0 hL M
      have hs' : (E N0 (2 ^ (M + 1)) : ℝ) ≤ (E N0 (2 ^ M) : ℝ) +
          (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (Exc N0)).card : ℝ) := by
        exact_mod_cast hsplit
      have h2 : (2:ℝ) ^ (M + 1) = 2 * 2 ^ M := by ring
      have hshell' : (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (Exc N0)).card : ℝ) ≤
          D * ((M : ℝ) + 1) * 2 ^ M := by
        calc _ ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)) := hshell
          _ = D * ((M : ℝ) + 1) * 2 ^ M := by rw [hD]; ring
      push_cast
      rw [h2]
      have hP : (0:ℝ) ≤ D * 2 ^ M := by positivity
      nlinarith
  unfold e
  rw [div_le_iff₀ (by positivity)]
  calc (E N0 (2 ^ M) : ℝ) ≤ D * M * 2 ^ M := key M
    _ = C * (M : ℝ) * ((L : ℝ) + 1) * Real.exp (-(c * L)) * 2 ^ M := by rw [hD]; ring

/-- The base window: if `y ≥ 2^{10000}`, then `p(N0, y) ≤ 16 C (α log₂ y + 1)(L+1) e^{-cL}`. -/
lemma window_fixed (C c : ℝ) (hC : 0 < C) (L0 : ℕ)
    (hB : ∀ L M : ℕ, L0 ≤ L → L ≤ M →
      (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (fun n => ∀ k, 2 ^ L ≤ T^[k] n)).card : ℝ)
        ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)))
    (N0 : ℕ) (hN0 : 1 ≤ N0) (hL : L0 ≤ Nat.log 2 N0) (y : ℝ) (hy : (2:ℝ) ^ (10000:ℕ) ≤ y) :
    p N0 y ≤ 16 * (C * (alpha * Real.logb 2 y + 2) * ((Nat.log 2 N0 : ℝ) + 1) *
      Real.exp (-(c * Nat.log 2 N0))) := by
  apply window_blocks N0 y hy
  intro ℓ hℓ
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hfl : ⌊y ^ alpha⌋₊ ≠ 0 := by
    have hgap := dyadic_log_gap hy
    intro h0
    rw [h0, Nat.log_zero_right] at hgap
    omega
  have ha1 : ((Nat.log 2 ⌊y ^ alpha⌋₊ : ℕ) : ℝ) ≤ alpha * Real.logb 2 y := dyadic_log_floor_le hy0 hfl
  have hℓ1 : (ℓ : ℝ) ≤ alpha * Real.logb 2 y := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hℓ).2) ha1
  have he := e_fixed C c hC L0 hB N0 hN0 hL (ℓ + 1)
  have hK : 0 ≤ C * (((Nat.log 2 N0 : ℕ) : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := by positivity
  calc e N0 (ℓ + 1) ≤ C * ((ℓ + 1 : ℕ) : ℝ) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := he
    _ ≤ C * (alpha * Real.logb 2 y + 2) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := by
        push_cast
        have : (ℓ:ℝ) + 1 ≤ alpha * Real.logb 2 y + 2 := by linarith
        have hC' : 0 ≤ C := hC.le
        gcongr

/-- Large windows: build upward from `X1 = e^v` with the one-step recursion. For all `y ≥ X1^α`,
`p(N0, y) ≤ 16 C (α³ v / log 2 + 2)(L+1) e^{-cL} + K1 v^{-cs}`. -/
lemma window_uniform (C c : ℝ) (hC : 0 < C) (L0 : ℕ)
    (hB : ∀ L M : ℕ, L0 ≤ L → L ≤ M →
      (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (fun n => ∀ k, 2 ^ L ≤ T^[k] n)).card : ℝ)
        ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)))
    (Cs cs Xs : ℝ) (hCs : 0 ≤ Cs) (hcs : 0 < cs) (hStep : StepHyp Cs cs Xs)
    (N0 : ℕ) (hN0 : 1 ≤ N0) (hL : L0 ≤ Nat.log 2 N0) (v : ℝ) (hv : 0 < v)
    (hbig : (2:ℝ) ^ (10000:ℕ) ≤ Real.exp v) (hXs : Xs ≤ Real.exp v) (hN0v : (N0:ℝ) ≤ Real.exp v) :
    ∀ y : ℝ, (Real.exp v) ^ alpha ≤ y →
      p N0 y ≤ 16 * (C * (alpha ^ 3 * v / Real.log 2 + 2) * ((Nat.log 2 N0 : ℝ) + 1) *
        Real.exp (-(c * Nat.log 2 N0))) + 2 * Cs / (1 - alpha ^ (-cs)) * v ^ (-cs) := by
  intro y hy
  have ha := alpha_pos
  have ha1 := alpha_gt_one
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set X1 := Real.exp v with hX1def
  have hX1 : 1 < X1 := Real.one_lt_exp_iff.mpr hv
  obtain ⟨J, x1, hx1lo, hx1hi, hyx⟩ := represent X1 y hX1 hy
  have hx1 : 1 < x1 := lt_of_lt_of_le hX1 hx1lo
  have hstep := p_iter_step Cs cs Xs hStep N0 hN0 x1 hx1.le (le_trans hXs hx1lo)
    (le_trans hN0v hx1lo) J
  have herr := err_sum_step Cs cs x1 hCs hcs hx1 J
  have hlx1 : v ≤ Real.log x1 := by
    rw [← Real.log_exp v]; exact Real.log_le_log (Real.exp_pos v) hx1lo
  have hlx1' : Real.log x1 < alpha * v := by
    have := Real.log_lt_log (lt_trans one_pos hx1) hx1hi
    rwa [Real.log_rpow (Real.exp_pos v), Real.log_exp] at this
  have hvpow : (Real.log x1) ^ (-cs) ≤ v ^ (-cs) :=
    Real.rpow_le_rpow_of_nonpos hv hlx1 (by linarith)
  set y' := x1 ^ alpha with hy'def
  have hx1y' : x1 ≤ y' := by
    calc x1 = x1 ^ (1:ℝ) := (Real.rpow_one x1).symm
      _ ≤ x1 ^ alpha := Real.rpow_le_rpow_of_exponent_le hx1.le ha1.le
  have hy'big : (2:ℝ) ^ (10000:ℕ) ≤ y' := le_trans hbig (le_trans hx1lo hx1y')
  have hbase := window_fixed C c hC L0 hB N0 hN0 hL y' hy'big
  have hlog2y : alpha * Real.logb 2 y' + 2 ≤ alpha ^ 3 * v / Real.log 2 + 2 := by
    have h1 : Real.logb 2 y' = alpha * Real.log x1 / Real.log 2 := by
      rw [Real.logb, Real.log_rpow (lt_trans one_pos hx1)]
    rw [h1]
    have h2 : alpha * (alpha * Real.log x1 / Real.log 2) ≤ alpha ^ 3 * v / Real.log 2 := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hl2]
      have : alpha * (alpha * Real.log x1) = alpha ^ 2 * Real.log x1 := by ring
      rw [this, show alpha ^ 3 * v = alpha ^ 2 * (alpha * v) by ring]
      exact mul_le_mul_of_nonneg_left hlx1'.le (by positivity)
    linarith
  have hK : 0 ≤ C * (((Nat.log 2 N0 : ℕ) : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := by positivity
  rw [hyx]
  calc p N0 (x1 ^ (alpha ^ (J + 1)))
      ≤ p N0 (x1 ^ alpha) + ∑ j ∈ Finset.range J, Cs * (Real.log (x1 ^ (alpha ^ j))) ^ (-cs) := hstep
    _ ≤ 16 * (C * (alpha * Real.logb 2 y' + 2) * ((Nat.log 2 N0 : ℝ) + 1) *
          Real.exp (-(c * Nat.log 2 N0))) + 2 * Cs / (1 - alpha ^ (-cs)) * (Real.log x1) ^ (-cs) :=
        add_le_add hbase herr
    _ ≤ _ := by
        have hK1 : 0 ≤ 2 * Cs / (1 - alpha ^ (-cs)) := by
          have : alpha ^ (-cs) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha1 (by linarith)
          apply div_nonneg (by linarith) (by linarith)
        have hC' : 0 ≤ C := hC.le
        gcongr

/-- The top (with a general window estimate `P`): if `X ≥ (e^v)^{α²}`, then the ratio is `≤ Kt(64000 v^{-1} + v^{-1/40}) + 2P`. -/
lemma top_generic (Kt x0 P v : ℝ) (N0 : ℕ) (hKt : 0 ≤ Kt) (hv1 : 1 ≤ v) (hx0e : x0 ≤ Real.exp v)
    (htop : ∀ X : ℝ, 1 ≤ X → x0 ≤ Erdos1135.Tao.taoSection3AmbientBoundary X 2 →
        Erdos1135.ND.oddSyracuseBadRatio N0 X ≤
          Kt * (X ^ (-(1 / 32000 : ℝ)) + (Erdos1135.Tao.taoSection3AmbientBoundary X 2) ^ (-(1 / 32000 : ℝ)) +
            (Real.log (Erdos1135.Tao.taoSection3AmbientBoundary X 2)) ^ (-(1 / 40 : ℝ))) +
          2 * p N0 (Erdos1135.Tao.taoSection3AmbientBoundary X 1))
    (hwin : ∀ y : ℝ, (Real.exp v) ^ alpha ≤ y → p N0 y ≤ P)
    (X : ℝ) (hX : (Real.exp v) ^ (alpha ^ 2) ≤ X) :
    Erdos1135.ND.oddSyracuseBadRatio N0 X ≤ Kt * (64000 * v⁻¹ + v ^ (-(1 / 40 : ℝ))) + 2 * P := by
  have ha := alpha_pos
  have ha1 := alpha_gt_one
  have hv0 : 0 < v := by linarith
  have hev0 : 0 < Real.exp v := Real.exp_pos v
  have hX1 : 1 ≤ X := le_trans (Real.one_le_rpow (Real.one_le_exp hv0.le) (by positivity)) hX
  have hq : Erdos1135.Tao.taoSection3AmbientBoundary X 2 = X ^ (alpha ^ 2)⁻¹ := by
    unfold Erdos1135.Tao.taoSection3AmbientBoundary Erdos1135.Tao.taoSection3AmbientRatio
    rw [← alpha_eq_tao, inv_pow]
  have hy : Erdos1135.Tao.taoSection3AmbientBoundary X 1 = X ^ alpha⁻¹ := by
    unfold Erdos1135.Tao.taoSection3AmbientBoundary Erdos1135.Tao.taoSection3AmbientRatio
    rw [← alpha_eq_tao, pow_one]
  have hqge : Real.exp v ≤ Erdos1135.Tao.taoSection3AmbientBoundary X 2 := by
    rw [hq]
    calc Real.exp v = ((Real.exp v) ^ (alpha ^ 2)) ^ (alpha ^ 2)⁻¹ := by
          rw [← Real.rpow_mul hev0.le, mul_inv_cancel₀ (by positivity), Real.rpow_one]
      _ ≤ X ^ (alpha ^ 2)⁻¹ := Real.rpow_le_rpow (by positivity) hX (by positivity)
  have hyge : (Real.exp v) ^ alpha ≤ Erdos1135.Tao.taoSection3AmbientBoundary X 1 := by
    rw [hy]
    calc (Real.exp v) ^ alpha = ((Real.exp v) ^ (alpha ^ 2)) ^ alpha⁻¹ := by
          rw [← Real.rpow_mul hev0.le]; congr 1; field_simp
      _ ≤ X ^ alpha⁻¹ := Real.rpow_le_rpow (by positivity) hX (by positivity)
  have hXge : Real.exp v ≤ X := by
    calc Real.exp v = (Real.exp v) ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.exp v) ^ (alpha ^ 2) :=
          Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hv0.le) (by nlinarith)
      _ ≤ X := hX
  have htop' := htop X hX1 (le_trans hx0e hqge)
  have hp := hwin _ hyge
  set q := Erdos1135.Tao.taoSection3AmbientBoundary X 2 with hqdef
  have he : (Real.exp v) ^ (-(1 / 32000 : ℝ)) ≤ 32000 * v⁻¹ := by
    rw [← Real.exp_mul]
    have := exp_neg_le_inv (v / 32000) (by positivity)
    have e1 : v * -(1 / 32000 : ℝ) = -(v / 32000) := by ring
    rw [e1]
    calc Real.exp (-(v / 32000)) ≤ (v / 32000)⁻¹ := this
      _ = 32000 * v⁻¹ := by field_simp
  have hXa : X ^ (-(1 / 32000 : ℝ)) ≤ 32000 * v⁻¹ :=
    le_trans (Real.rpow_le_rpow_of_nonpos hev0 hXge (by norm_num)) he
  have hqa : q ^ (-(1 / 32000 : ℝ)) ≤ 32000 * v⁻¹ :=
    le_trans (Real.rpow_le_rpow_of_nonpos hev0 hqge (by norm_num)) he
  have hlq : v ≤ Real.log q := by
    rw [← Real.log_exp v]; exact Real.log_le_log hev0 hqge
  have hla : (Real.log q) ^ (-(1 / 40 : ℝ)) ≤ v ^ (-(1 / 40 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hv0 hlq (by norm_num)
  have h1 : X ^ (-(1 / 32000 : ℝ)) + q ^ (-(1 / 32000 : ℝ)) + (Real.log q) ^ (-(1 / 40 : ℝ)) ≤
      64000 * v⁻¹ + v ^ (-(1 / 40 : ℝ)) := by linarith
  have h3 := mul_le_mul_of_nonneg_left h1 hKt
  calc Erdos1135.ND.oddSyracuseBadRatio N0 X ≤ _ := htop'
    _ ≤ Kt * (64000 * v⁻¹ + v ^ (-(1 / 40 : ℝ))) + 2 * P := by linarith

/-- Small `X` (`X < (e^v)^{α²}`): the ratio is `≤ 2 C (α² v / log 2 + 1)(L+1) e^{-cL}`. -/
lemma small_uniform (C c : ℝ) (hC : 0 < C) (L0 : ℕ)
    (hB : ∀ L M : ℕ, L0 ≤ L → L ≤ M →
      (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter (fun n => ∀ k, 2 ^ L ≤ T^[k] n)).card : ℝ)
        ≤ C * 2 ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(c * L)))
    (N0 : ℕ) (hN0 : 1 ≤ N0) (hL : L0 ≤ Nat.log 2 N0) (v : ℝ) (hv : 0 < v)
    (X : ℝ) (hX2 : 2 ≤ X) (hX : X < (Real.exp v) ^ (alpha ^ 2)) :
    Erdos1135.ND.oddSyracuseBadRatio N0 X ≤
      2 * (C * (alpha ^ 2 * v / Real.log 2 + 1) * ((Nat.log 2 N0 : ℝ) + 1) *
        Real.exp (-(c * Nat.log 2 N0))) := by
  have ha := alpha_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set F := ⌊X⌋₊ with hF
  have hX0 : 0 < X := by linarith
  have hF2 : 2 ≤ F := Nat.le_floor (by exact_mod_cast hX2)
  have hF0 : F ≠ 0 := by omega
  have hFX : (F : ℝ) ≤ X := Nat.floor_le hX0.le
  set t := Nat.log 2 F + 1 with ht
  have hFt : F < 2 ^ t := Nat.lt_pow_succ_log_self (by norm_num) F
  have htF : 2 ^ t ≤ 2 * F := by
    rw [ht, pow_succ]; have := Nat.pow_log_le_self 2 hF0; omega
  -- `t ≤ α² v / log 2 + 1`
  have htv : (t : ℝ) ≤ alpha ^ 2 * v / Real.log 2 + 1 := by
    have h1 : (2:ℝ) ^ (Nat.log 2 F) ≤ F := by exact_mod_cast Nat.pow_log_le_self 2 hF0
    have h2 : ((Nat.log 2 F : ℕ) : ℝ) * Real.log 2 ≤ Real.log X := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) (le_trans h1 hFX)
    have h3 : Real.log X < alpha ^ 2 * v := by
      have := Real.log_lt_log hX0 hX
      rwa [Real.log_rpow (Real.exp_pos v), Real.log_exp] at this
    have h4 : ((Nat.log 2 F : ℕ) : ℝ) ≤ alpha ^ 2 * v / Real.log 2 := by
      rw [le_div_iff₀ hl2]; linarith
    rw [ht]; push_cast; linarith
  have he := e_fixed C c hC L0 hB N0 hN0 hL t
  have hcount : (Erdos1135.ND.natCountLEReal (Erdos1135.ND.oddSyracuseBadSet N0) X : ℝ) ≤
      (E N0 (2 ^ t) : ℝ) := by
    unfold Erdos1135.ND.natCountLEReal Erdos1135.ND.natCountLE
    rw [← hF]
    exact_mod_cast le_trans (natCount_le_E N0 (F + 1)) (E_mono N0 (by omega))
  have hE : (E N0 (2 ^ t) : ℝ) ≤ (C * (t : ℝ) * ((Nat.log 2 N0 : ℝ) + 1) *
      Real.exp (-(c * Nat.log 2 N0))) * 2 ^ t := by
    unfold e at he
    rw [div_le_iff₀ (by positivity)] at he
    exact he
  have h2t : ((2 ^ t : ℕ) : ℝ) ≤ 2 * X := by
    have : ((2 ^ t : ℕ) : ℝ) ≤ 2 * (F : ℝ) := by exact_mod_cast htF
    linarith
  push_cast at h2t
  have hK : 0 ≤ C * (((Nat.log 2 N0 : ℕ) : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := by positivity
  have hct : C * (t : ℝ) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) ≤
      C * (alpha ^ 2 * v / Real.log 2 + 1) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := by
    have hC' : 0 ≤ C := hC.le
    gcongr
  unfold Erdos1135.ND.oddSyracuseBadRatio
  rw [div_le_iff₀ hX0]
  have hQ : 0 ≤ C * (t : ℝ) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0)) := by positivity
  calc (Erdos1135.ND.natCountLEReal (Erdos1135.ND.oddSyracuseBadSet N0) X : ℝ)
      ≤ (C * (t : ℝ) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0))) * 2 ^ t :=
        le_trans hcount hE
    _ ≤ (C * (t : ℝ) * ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c * Nat.log 2 N0))) * (2 * X) := by
        gcongr
    _ ≤ (C * (alpha ^ 2 * v / Real.log 2 + 1) * ((Nat.log 2 N0 : ℝ) + 1) *
          Real.exp (-(c * Nat.log 2 N0))) * (2 * X) := by gcongr
    _ = 2 * (C * (alpha ^ 2 * v / Real.log 2 + 1) * ((Nat.log 2 N0 : ℝ) + 1) *
          Real.exp (-(c * Nat.log 2 N0))) * X := by ring

/-- `(L+1) e^{-c1 L} ≤ (1 + 2/c1) e^{c1/2} N0^{-c1/(2 log 2)}` (where `L = ⌊log₂ N0⌋`). -/
lemma rate_to_N0 (c1 : ℝ) (hc1 : 0 < c1) (N0 : ℕ) (hN0 : 1 ≤ N0) :
    ((Nat.log 2 N0 : ℝ) + 1) * Real.exp (-(c1 * Nat.log 2 N0)) ≤
      (1 + 2 / c1) * Real.exp (c1 / 2) * (N0 : ℝ) ^ (-(c1 / (2 * Real.log 2))) := by
  set L := Nat.log 2 N0 with hLdef
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : (0:ℝ) ≤ L := Nat.cast_nonneg L
  have hN0pos : (0:ℝ) < N0 := by exact_mod_cast (by omega : 0 < N0)
  -- `L e^{-c1 L/2} ≤ 2/c1`
  have h1 : (L:ℝ) * Real.exp (-(c1 * L / 2)) ≤ 2 / c1 := by
    have := Real.add_one_le_exp (c1 * L / 2)
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
    nlinarith
  have h2 : Real.exp (-(c1 * L / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hsplit : Real.exp (-(c1 * L)) = Real.exp (-(c1 * L / 2)) * Real.exp (-(c1 * L / 2)) := by
    rw [← Real.exp_add]; ring_nf
  -- `e^{-c1 L/2} ≤ e^{c1/2} N0^{-c1/(2 log 2)}`
  have hN0lt : (N0:ℝ) < 2 ^ (L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N0
  have hlogN0 : Real.log N0 < ((L:ℝ) + 1) * Real.log 2 := by
    have := Real.log_lt_log hN0pos hN0lt
    rw [Real.log_pow] at this; push_cast at this; linarith
  have h3 : Real.exp (-(c1 * L / 2)) ≤ Real.exp (c1 / 2) * (N0 : ℝ) ^ (-(c1 / (2 * Real.log 2))) := by
    rw [Real.rpow_def_of_pos hN0pos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : Real.log N0 * (c1 / (2 * Real.log 2)) ≤ ((L:ℝ) + 1) * Real.log 2 * (c1 / (2 * Real.log 2)) :=
      mul_le_mul_of_nonneg_right hlogN0.le (by positivity)
    have e1 : ((L:ℝ) + 1) * Real.log 2 * (c1 / (2 * Real.log 2)) = c1 * (L + 1) / 2 := by
      field_simp
    nlinarith
  have hA : 0 ≤ Real.exp (-(c1 * L / 2)) := (Real.exp_pos _).le
  calc ((L : ℝ) + 1) * Real.exp (-(c1 * L))
      = ((L:ℝ) * Real.exp (-(c1 * L / 2)) + Real.exp (-(c1 * L / 2))) * Real.exp (-(c1 * L / 2)) := by
        rw [hsplit]; ring
    _ ≤ (2 / c1 + 1) * Real.exp (-(c1 * L / 2)) := by
        apply mul_le_mul_of_nonneg_right _ hA; linarith
    _ ≤ (2 / c1 + 1) * (Real.exp (c1 / 2) * (N0 : ℝ) ^ (-(c1 / (2 * Real.log 2)))) := by
        gcongr
    _ = (1 + 2 / c1) * Real.exp (c1 / 2) * (N0 : ℝ) ^ (-(c1 / (2 * Real.log 2))) := by ring

/-- Bound the powers of `v = e^{cL/2}` and `e^{-cL}` by `e^{-c1 L}` (where `c1 = c·min(1/80, cs/2)`). -/
lemma v_facts (c cs L v c1 : ℝ) (hc : 0 < c) (hcs : 0 < cs) (hL : 0 ≤ L)
    (hv : v = Real.exp (c * L / 2)) (hc1 : c1 = c * min (1 / 80) (cs / 2)) :
    v * Real.exp (-(c * L)) ≤ Real.exp (-(c1 * L)) ∧ Real.exp (-(c * L)) ≤ Real.exp (-(c1 * L)) ∧
    v⁻¹ ≤ Real.exp (-(c1 * L)) ∧ v ^ (-(1 / 40 : ℝ)) ≤ Real.exp (-(c1 * L)) ∧
    v ^ (-cs) ≤ Real.exp (-(c1 * L)) := by
  have hm1 : min (1 / 80 : ℝ) (cs / 2) ≤ 1 / 80 := min_le_left _ _
  have hm2 : min (1 / 80 : ℝ) (cs / 2) ≤ cs / 2 := min_le_right _ _
  have hm0 : 0 < min (1 / 80 : ℝ) (cs / 2) := lt_min (by norm_num) (by linarith)
  have hc1a : c1 * L ≤ c * L / 80 := by
    have : c1 ≤ c / 80 := by
      rw [hc1]
      calc c * min (1 / 80) (cs / 2) ≤ c * (1 / 80) := mul_le_mul_of_nonneg_left hm1 hc.le
        _ = c / 80 := by ring
    nlinarith
  have hc1b : c1 * L ≤ cs * (c * L / 2) := by
    have : c1 ≤ c * (cs / 2) := by rw [hc1]; exact mul_le_mul_of_nonneg_left hm2 hc.le
    nlinarith
  have hc1pos : 0 ≤ c1 * L := by rw [hc1]; exact mul_nonneg (mul_pos hc hm0).le hL
  have hlogv : Real.log v = c * L / 2 := by rw [hv]; exact Real.log_exp _
  have hvpos : 0 < v := by rw [hv]; exact Real.exp_pos _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hv, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  · apply Real.exp_le_exp.mpr; nlinarith
  · rw [hv, ← Real.exp_neg]; apply Real.exp_le_exp.mpr; nlinarith
  · rw [Real.rpow_def_of_pos hvpos, hlogv]
    apply Real.exp_le_exp.mpr; nlinarith
  · rw [Real.rpow_def_of_pos hvpos, hlogv]
    apply Real.exp_le_exp.mpr; nlinarith

/-- Arithmetic (small `X`). -/
lemma arith_small (R C a v eL eL1 L : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hL : 0 ≤ L + 1)
    (h : R ≤ 2 * (C * (a * v + 1) * (L + 1) * eL)) (fa : v * eL ≤ eL1) (fb : eL ≤ eL1) :
    R ≤ 2 * C * (a + 1) * ((L + 1) * eL1) := by
  have h1 : (a * v + 1) * eL ≤ (a + 1) * eL1 := by nlinarith
  have h2 : C * (L + 1) * ((a * v + 1) * eL) ≤ C * (L + 1) * ((a + 1) * eL1) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hL)
  nlinarith

/-- Arithmetic (large `X`). -/
lemma arith_large (R Kt C a K1 v vinv v40 vcs eL eL1 L : ℝ) (hKt : 0 ≤ Kt) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hK1 : 0 ≤ K1) (hL : 1 ≤ L + 1) (heL1 : 0 ≤ eL1)
    (h : R ≤ Kt * (64000 * vinv + v40) + 2 * (16 * (C * (a * v + 2) * (L + 1) * eL) + K1 * vcs))
    (fa : v * eL ≤ eL1) (fb : eL ≤ eL1) (fc : vinv ≤ eL1) (fd : v40 ≤ eL1) (fe : vcs ≤ eL1) :
    R ≤ (Kt * 64001 + 2 * (16 * C * (a + 2) + K1)) * ((L + 1) * eL1) := by
  have hLe : eL1 ≤ (L + 1) * eL1 := by nlinarith
  have h1 : 64000 * vinv + v40 ≤ 64001 * ((L + 1) * eL1) := by nlinarith
  have h2 : (a * v + 2) * eL ≤ (a + 2) * eL1 := by nlinarith
  have h3 : C * (L + 1) * ((a * v + 2) * eL) ≤ C * (L + 1) * ((a + 2) * eL1) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hC (by linarith))
  have h4 : K1 * vcs ≤ K1 * ((L + 1) * eL1) := mul_le_mul_of_nonneg_left (le_trans fe hLe) hK1
  have h5 : Kt * (64000 * vinv + v40) ≤ Kt * (64001 * ((L + 1) * eL1)) := mul_le_mul_of_nonneg_left h1 hKt
  nlinarith

/-- **Syracuse form of Theorem 1.1 of the paper (the bound on `ρ(N0, X)` in Section 6; under the hypothesis `FixedBarrierHyp`)**: there are `K, c' > 0` such that for all
`N0 ≥ 1` and `X ≥ 2`, `#{N ≤ X odd : Syr_min(N) > N0}/X ≤ K N0^{-c'}` (a power saving uniform in `X`). -/
theorem nd_syracuse_uniform_of_fixedBarrier (hFB : FixedBarrierHyp) :
    ∃ K c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℝ, 2 ≤ X →
      Erdos1135.ND.oddSyracuseBadRatio N0 X ≤ K * (N0 : ℝ) ^ (-c') := by
  obtain ⟨C, c, hC, hc, L0, hB⟩ := hFB
  obtain ⟨Cs, cs, Xs, hCs, hcs, hStep⟩ := stepHyp_nd
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
  refine ⟨K, c', hc', ?_⟩
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

/-- **Theorem 1.1 of the paper (Collatz form, under the hypothesis `FixedBarrierHyp`)**: there are `K, c' > 0` such that for all
`N0 ≥ 1` and all `X`, `#{1 ≤ N ≤ X : Col_min(N) > N0} ≤ K N0^{-c'} X`. -/
theorem nd_collatz_uniform_of_fixedBarrier (hFB : FixedBarrierHyp) :
    ∃ K c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
      (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) ≤
        K * (N0 : ℝ) ^ (-c') * X := by
  obtain ⟨K, c', hc', h⟩ := nd_syracuse_uniform_of_fixedBarrier hFB
  refine ⟨2 * K, c', hc', ?_⟩
  intro N0 hN0 X
  set ε := K * (N0 : ℝ) ^ (-c') with hε
  have hε0 : 0 ≤ ε := by
    have h2 := h N0 hN0 2 le_rfl
    have : 0 ≤ Erdos1135.ND.oddSyracuseBadRatio N0 2 := by
      unfold Erdos1135.ND.oddSyracuseBadRatio; positivity
    linarith
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
    _ = 2 * K * (N0 : ℝ) ^ (-c') * X := by rw [hε]; ring

end Collatz
