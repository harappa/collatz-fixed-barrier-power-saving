import CollatzND.Core.Explicit

/-!
# Corollaries of the main theorem in the language of densities (Corollary 1.2 of the paper)

From the main theorem `Collatz.nd_collatz_uniform_explicit` (there is `K > 0` such that for all `N0 ≥ 1` and `X ∈ ℕ`,
`#{1 ≤ N ≤ X | Col_min(N) > N0} ≤ K N0^{-c'} X` with `c' = tstarExponent`) we derive, with the same `K` and `c'`:

* (i) **Upper density**: for every `N0 ≥ 1`, the ratio `#{1 ≤ N ≤ X | Col_min(N) > N0}/X` (`X ∈ ℕ`) is bounded
  above and its `limsup_{X → ∞}` is at most `K N0^{-c'}` (the ratio lies in `[0, 1]`, so the `limsup` is a genuine
  upper limit of reals; the boundedness is part of the statement).
* (ii) **Natural density one** (`nd_density_one`): if `f(N) → ∞`, then `{N | Col_min(N) < f(N)}` has natural density 1.
* (iii) Barrier `X^θ`: for `θ > 0` and real `X ≥ 1`, `#{1 ≤ N ≤ X | Col_min(N) > X^θ} ≤ 2^{c'} K X^{1-θc'}`
  (the paper states `θ ∈ (0, 1]`; the proof works for every `θ > 0`).

The proofs are those of the paper (elementary): (iii) takes `N0 = ⌊X^θ⌋₊ ≥ X^θ/2`; for (ii), fix `N0`; since
`f(N) > N0` for all but finitely many `N`, the complement lies in `[1, N₁] ∪ {Col_min > N0}`. The argument follows
the corresponding corollary of the author's paper on generalized Collatz maps (`lean-ggm/GGMCollatz/Corollary.lean` in the source repository).

In the statements, `Col_min(N) > b` is written `∀ m, b < col^[m] N` and `Col_min(N) < y` is written
`∃ m, col^[m] N < y`. The correspondence with `Col_min(N) = min_{m ≥ 0} col^m(N)` (`colMin`) is given by
`lt_colMin_iff` and `colMin_lt_iff`.
-/

namespace Collatz

open Classical

/-- `Col_min(N) = min_{m ≥ 0} col^m(N)` (the notation of the paper; `col^[0] = id`). -/
noncomputable def colMin (N : ℕ) : ℕ := sInf (Set.range fun m => col^[m] N)

/-- The minimum is attained on the orbit. -/
lemma colMin_mem (N : ℕ) : ∃ m, col^[m] N = colMin N := by
  have hne : (Set.range fun m => col^[m] N).Nonempty := ⟨N, 0, rfl⟩
  exact Nat.sInf_mem hne

lemma colMin_le (N m : ℕ) : colMin N ≤ col^[m] N :=
  Nat.sInf_le ⟨m, rfl⟩

/-- `b < Col_min(N)` is equivalent to `∀ m, b < col^m(N)`. -/
theorem lt_colMin_iff (b : ℝ) (N : ℕ) : b < (colMin N : ℝ) ↔ ∀ m, b < ((col^[m] N : ℕ) : ℝ) := by
  constructor
  · intro h m
    exact lt_of_lt_of_le h (by exact_mod_cast colMin_le N m)
  · intro h
    obtain ⟨m, hm⟩ := colMin_mem N
    rw [← hm]
    exact h m

/-- `Col_min(N) < y` is equivalent to `∃ m, col^m(N) < y`. -/
theorem colMin_lt_iff (y : ℝ) (N : ℕ) : (colMin N : ℝ) < y ↔ ∃ m, ((col^[m] N : ℕ) : ℝ) < y := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := colMin_mem N
    exact ⟨m, by rw [hm]; exact h⟩
  · rintro ⟨m, hm⟩
    exact lt_of_le_of_lt (by exact_mod_cast colMin_le N m) hm

namespace Density

/-- The inequality of the main theorem (the body of `nd_collatz_uniform_explicit`, exponent `c`). -/
def MainIneq (K c : ℝ) : Prop :=
  ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
    (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) ≤
      K * (N0 : ℝ) ^ (-c) * X

/-- The main theorem in the form `MainIneq K tstarExponent`. -/
theorem mainIneq_explicit : ∃ K : ℝ, 0 < K ∧ MainIneq K tstarExponent :=
  nd_collatz_uniform_explicit

variable {K c : ℝ}

/-- The ratio form for `X ≥ 1`: `#{1 ≤ N ≤ X | Col_min(N) > N0}/X ≤ K N0^{-c}`. -/
theorem ratio_le (hmain : MainIneq K c) {N0 : ℕ} (hN0 : 1 ≤ N0) {X : ℕ} (hX : 1 ≤ X) :
    (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) / X ≤
      K * (N0 : ℝ) ^ (-c) := by
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  rw [div_le_iff₀ hX']
  exact hmain N0 hN0 X

/-- (i): the ratio is bounded above and its `limsup_{X → ∞}` is at most `K N0^{-c}`. -/
theorem upper_density (hmain : MainIneq K c) {N0 : ℕ} (hN0 : 1 ≤ N0) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) / X) ∧
      Filter.limsup
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) / X)
          Filter.atTop ≤ K * (N0 : ℝ) ^ (-c) := by
  have hev : ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) / X ≤
        K * (N0 : ℝ) ^ (-c) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with X hX
    exact ratio_le hmain hN0 hX
  refine ⟨Filter.isBoundedUnder_of_eventually_le hev, ?_⟩
  exact Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le Filter.atTop fun X => by positivity) hev

/-- If `t ≥ 1` then `t/2 ≤ ⌊t⌋₊`. -/
theorem half_le_floor {t : ℝ} (ht : 1 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have h1 := Nat.sub_one_lt_floor t
  have h2 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have h2' : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast h2
  linarith

/-- (iii): for `θ > 0` and real `X ≥ 1`, `#{1 ≤ N ≤ X | Col_min(N) > X^θ} ≤ 2^c K X^{1-θc}`
(take `N0 = ⌊X^θ⌋₊ ≥ X^θ/2`). -/
theorem count_Xpow (hK : 0 < K) (hc : 0 < c) (hmain : MainIneq K c) {θ : ℝ} (hθ : 0 < θ)
    {X : ℝ} (hX : 1 ≤ X) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => ∀ m, X ^ θ < ((col^[m] N : ℕ) : ℝ))).card : ℝ) ≤
      2 ^ c * K * X ^ (1 - θ * c) := by
  have hX0 : 0 < X := by linarith
  set b : ℝ := X ^ θ with hbdef
  have hb : 1 ≤ b := Real.one_le_rpow hX hθ.le
  set N0 := ⌊b⌋₊ with hN0
  have hN01 : 1 ≤ N0 := Nat.le_floor (by exact_mod_cast hb)
  have hN0b : (N0 : ℝ) ≤ b := Nat.floor_le (by linarith)
  have hhalf : b / 2 ≤ (N0 : ℝ) := half_le_floor hb
  have hsub : (Finset.Icc 1 ⌊X⌋₊).filter (fun N => ∀ m, b < ((col^[m] N : ℕ) : ℝ)) ⊆
      (Finset.Icc 1 ⌊X⌋₊).filter (fun N => ∀ m, N0 < col^[m] N) := by
    intro N hN
    rw [Finset.mem_filter] at hN ⊢
    refine ⟨hN.1, fun m => ?_⟩
    have : (N0 : ℝ) < ((col^[m] N : ℕ) : ℝ) := lt_of_le_of_lt hN0b (hN.2 m)
    exact_mod_cast this
  have hcard : (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => ∀ m, b < ((col^[m] N : ℕ) : ℝ))).card : ℝ) ≤
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h1 := hmain N0 hN01 ⌊X⌋₊
  have hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
  have hN0pos : (0 : ℝ) < N0 := by exact_mod_cast hN01
  have hKN : 0 ≤ K * (N0 : ℝ) ^ (-c) := by positivity
  have hb2 : 0 < b / 2 := by linarith
  have hpow : (N0 : ℝ) ^ (-c) ≤ (b / 2) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos hb2 hhalf (by linarith)
  have hdiv : (b / 2) ^ (-c) = 2 ^ c * b ^ (-c) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul]
    ring
  have hXb : X * b ^ (-c) = X ^ (1 - θ * c) := by
    rw [hbdef, ← Real.rpow_mul hX0.le, show (1 : ℝ) - θ * c = 1 + θ * (-c) by ring,
      Real.rpow_add hX0, Real.rpow_one]
  calc (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => ∀ m, b < ((col^[m] N : ℕ) : ℝ))).card : ℝ)
      ≤ K * (N0 : ℝ) ^ (-c) * ⌊X⌋₊ := hcard.trans h1
    _ ≤ K * (N0 : ℝ) ^ (-c) * X := mul_le_mul_of_nonneg_left hfl hKN
    _ ≤ K * (b / 2) ^ (-c) * X := by gcongr
    _ = 2 ^ c * K * (X * b ^ (-c)) := by rw [hdiv]; ring
    _ = 2 ^ c * K * X ^ (1 - θ * c) := by rw [hXb]

/-- (ii): from `MainIneq K c` (`c > 0`): if `f(N) → ∞`, then `#{1 ≤ N ≤ X | Col_min(N) < f(N)}/X → 1`. -/
theorem density_one_of (hc : 0 < c) (hmain : MainIneq K c) (f : ℕ → ℝ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∃ m, ((col^[m] N : ℕ) : ℝ) < f N)).card : ℝ) / X)
      Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- `N0 ≥ 1` with `K N0^{-c} < ε/2`
  have hlim : Filter.Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-c)) Filter.atTop (nhds 0) := by
    have h := ((tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop).const_mul K
    rw [mul_zero] at h
    exact h
  obtain ⟨N0, hN0ε, hN01⟩ :=
    ((hlim.eventually (Iio_mem_nhds (half_pos hε))).and (Filter.eventually_ge_atTop 1)).exists
  have hN0ε' : K * (N0 : ℝ) ^ (-c) < ε / 2 := hN0ε
  -- `f(N) ≥ N0 + 1` for `N ≥ N₁`
  obtain ⟨N₁, hN₁⟩ := Filter.tendsto_atTop_atTop.mp hf ((N0 : ℝ) + 1)
  -- `X` with `N₁/X < ε/2`
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (((tendsto_const_div_atTop_nhds_zero_nat (N₁ : ℝ)).eventually
      (Iio_mem_nhds (half_pos hε))).and (Filter.eventually_ge_atTop 1))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hN₁X, hX1⟩ := hX₀ X hX
  have hN₁X' : (N₁ : ℝ) / X < ε / 2 := hN₁X
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  set T := Finset.Icc 1 X with hT
  set A := T.filter (fun N => ∃ m, ((col^[m] N : ℕ) : ℝ) < f N) with hA
  set Bc := T.filter (fun N => ¬ ∃ m, ((col^[m] N : ℕ) : ℝ) < f N) with hBc
  have hsplit : A.card + Bc.card = X := by
    rw [hA, hBc, Finset.card_filter_add_card_filter_not, hT, Nat.card_Icc]
    omega
  -- the complement lies in `[1, N₁] ∪ {Col_min > N0}`
  have hsub : Bc ⊆ Finset.Icc 1 N₁ ∪ T.filter (fun N => ∀ m, N0 < col^[m] N) := by
    intro N hN
    rw [hBc, Finset.mem_filter] at hN
    obtain ⟨hNT, hNf⟩ := hN
    rw [Finset.mem_union]
    by_cases hNN : N < N₁
    · left
      rw [hT, Finset.mem_Icc] at hNT
      rw [Finset.mem_Icc]
      exact ⟨hNT.1, hNN.le⟩
    · right
      rw [Finset.mem_filter]
      refine ⟨hNT, fun m => ?_⟩
      have h1 := hN₁ N (not_lt.mp hNN)
      have h2 : (N0 : ℝ) < ((col^[m] N : ℕ) : ℝ) := by
        have := not_lt.mp (fun h => hNf ⟨m, h⟩)
        linarith
      exact_mod_cast h2
  have hBcard : (Bc.card : ℝ) ≤ N₁ + K * (N0 : ℝ) ^ (-c) * X := by
    have h1 : Bc.card ≤ N₁ + (T.filter (fun N => ∀ m, N0 < col^[m] N)).card := by
      calc Bc.card ≤ (Finset.Icc 1 N₁ ∪ T.filter (fun N => ∀ m, N0 < col^[m] N)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.Icc 1 N₁).card + (T.filter (fun N => ∀ m, N0 < col^[m] N)).card :=
            Finset.card_union_le _ _
        _ = N₁ + (T.filter (fun N => ∀ m, N0 < col^[m] N)).card := by rw [Nat.card_Icc]; omega
    have h2 := hmain N0 hN01 X
    have h1' : (Bc.card : ℝ) ≤ N₁ + ((T.filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) := by
      exact_mod_cast h1
    linarith
  -- `|A/X - 1| = Bc/X < ε`
  have hAeq : (A.card : ℝ) = X - Bc.card := by
    have : ((A.card + Bc.card : ℕ) : ℝ) = X := by exact_mod_cast hsplit
    push_cast at this
    linarith
  rw [Real.dist_eq, hAeq, show ((X : ℝ) - Bc.card) / X - 1 = -((Bc.card : ℝ) / X) by
    field_simp; ring, abs_neg, abs_of_nonneg (by positivity)]
  calc (Bc.card : ℝ) / X ≤ (N₁ + K * (N0 : ℝ) ^ (-c) * X) / X :=
        div_le_div_of_nonneg_right hBcard hXpos.le
    _ = N₁ / X + K * (N0 : ℝ) ^ (-c) := by field_simp
    _ < ε / 2 + ε / 2 := add_lt_add hN₁X' hN0ε'
    _ = ε := by ring

end Density

open Density

/-- **Corollary 1.2 (ii) of the paper: natural density one.** If `f(N) → ∞`, then `{N | Col_min(N) < f(N)}` has
natural density 1: `#{1 ≤ N ≤ X | ∃ m, col^m(N) < f(N)}/X → 1` (`X → ∞`, `X ∈ ℕ`).
The equivalence of `Col_min(N) < f(N)` and `∃ m, col^m(N) < f(N)` is `colMin_lt_iff`. -/
theorem nd_density_one (f : ℕ → ℝ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∃ m, ((col^[m] N : ℕ) : ℝ) < f N)).card : ℝ) / X)
      Filter.atTop (nhds 1) := by
  obtain ⟨K, -, hmain⟩ := mainIneq_explicit
  exact density_one_of tstarExponent_pos hmain f hf

/-- **Corollary 1.2 (i) and (iii) of the paper** (with the same `K` as the main theorem and `c' = tstarExponent`):
there is `K > 0` such that

* main theorem: for all `N0 ≥ 1` and `X ∈ ℕ`, `#{1 ≤ N ≤ X | Col_min(N) > N0} ≤ K N0^{-c'} X`;
* (i) for every `N0 ≥ 1`, the ratio `#{1 ≤ N ≤ X | Col_min(N) > N0}/X` (`X ∈ ℕ`) is bounded above and
  its `limsup_{X → ∞}` is at most `K N0^{-c'}`;
* (iii) for all `θ > 0` and real `X ≥ 1`, `#{1 ≤ N ≤ X | Col_min(N) > X^θ} ≤ 2^{c'} K X^{1-θc'}`.

(ii) is `nd_density_one`. -/
theorem nd_collatz_corollaries :
    ∃ K : ℝ, 0 < K ∧
      (∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
        (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) ≤
          K * (N0 : ℝ) ^ (-tstarExponent) * X) ∧
      (∀ N0 : ℕ, 1 ≤ N0 →
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) / X) ∧
        Filter.limsup
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) / X)
          Filter.atTop ≤ K * (N0 : ℝ) ^ (-tstarExponent)) ∧
      (∀ θ : ℝ, 0 < θ → ∀ X : ℝ, 1 ≤ X →
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => ∀ m, X ^ θ < ((col^[m] N : ℕ) : ℝ))).card : ℝ) ≤
          2 ^ tstarExponent * K * X ^ (1 - θ * tstarExponent)) := by
  obtain ⟨K, hK, hmain⟩ := mainIneq_explicit
  exact ⟨K, hK, hmain, fun N0 hN0 => upper_density hmain hN0,
    fun θ hθ X hX => count_Xpow hK tstarExponent_pos hmain hθ hX⟩

end Collatz
