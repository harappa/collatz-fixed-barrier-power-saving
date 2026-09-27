import CollatzProof.Core.TaoFinal
import CollatzProof.Core.Conv
import Erdos1135.ND.RhinUnconditional
import Erdos1135.ND.Discrepancy.A5ReferenceND31FullCount
import Erdos1135.ND.Discrepancy.A5ReferenceSection3GeometricBudget
import Erdos1135.Tao.Section3.FixedTargetPassage

/-!
# The part of `CollatzND.Bridge` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzND.Bridge` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzND.Bridge` in the source repository.
-/

namespace Collatz

open Classical

lemma alpha_eq_tao : alpha = Erdos1135.Tao.taoAlpha := by
  unfold alpha Erdos1135.Tao.taoAlpha; norm_num

lemma Syr_eq_syracuse : Syr = Erdos1135.Tao.syracuse := by
  funext N; rfl

lemma syrMinGT_iff_noHit (N0 N : ℕ) :
    SyrMinGT N0 N ↔ N ∈ Erdos1135.Tao.syracuseNoHitAtMost N0 := by
  unfold SyrMinGT Erdos1135.Tao.syracuseNoHitAtMost Erdos1135.Tao.syracuseHitsAtMost
  rw [Syr_eq_syracuse, Set.mem_setOf_eq]
  constructor
  · rintro h ⟨m, hm⟩; have := h m; omega
  · intro h k; by_contra hk; exact h ⟨k, by omega⟩

lemma W_eq_taoNy (y : ℝ) :
    W y = Erdos1135.Tao.taoNyOddWindow y Erdos1135.Tao.taoAlpha := by
  ext N
  unfold W Erdos1135.Tao.taoNyOddWindow Erdos1135.Tao.oddLogWindow Erdos1135.Tao.taoNyLo
    Erdos1135.Tao.taoNyHi
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, ← alpha_eq_tao]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨Nat.ceil_le.mpr h3, by omega⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3, Nat.ceil_le.mp h1⟩

lemma wt_eq_logNatWeight (N : ℕ) : wt N = Erdos1135.Tao.logNatWeight N := by
  unfold wt Erdos1135.Tao.logNatWeight Erdos1135.Tao.logWeight
  split_ifs with h
  · subst h; simp
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h), one_div]

/-- `p N0 y` is the probability, on Mazur's logarithmically uniform window, of never reaching a value `≤ N0`. -/
lemma p_eq_logFinsetProb (N0 : ℕ) (y : ℝ) :
    p N0 y = Erdos1135.Tao.logFinsetProb (Erdos1135.Tao.taoNyOddWindow y Erdos1135.Tao.taoAlpha)
      (Erdos1135.Tao.syracuseNoHitAtMost N0) := by
  unfold p prob Zw Erdos1135.Tao.logFinsetProb Erdos1135.Tao.logFinsetMass
  rw [← W_eq_taoNy y]
  congr 1
  · apply Finset.sum_congr
    · ext N; simp only [Finset.mem_filter, syrMinGT_iff_noHit]
    · intro N _; exact wt_eq_logNatWeight N
  · exact Finset.sum_congr rfl fun N _ => wt_eq_logNatWeight N

/-- Complement of the window probability: `logFinsetProb W (good N0) = 1 − p`. -/
lemma good_eq_one_sub_p (N0 : ℕ) (y : ℝ)
    (hmass : 0 < Erdos1135.Tao.logFinsetMass
      (Erdos1135.Tao.oddLogWindow (Erdos1135.Tao.taoNyLo y)
        (Erdos1135.Tao.taoNyHi y Erdos1135.Tao.taoAlpha))) :
    Erdos1135.Tao.logFinsetProb
      (Erdos1135.Tao.oddLogWindow (Erdos1135.Tao.taoNyLo y)
        (Erdos1135.Tao.taoNyHi y Erdos1135.Tao.taoAlpha))
      (Erdos1135.Tao.syracuseThresholdGood N0) = 1 - p N0 y := by
  have h1 := Erdos1135.Tao.syracuseNoHitWindowProb_eq_one_sub_thresholdGoodProb N0 _ _ hmass
  have h2 : Erdos1135.Tao.syracuseNoHitWindowProb N0 _ _ hmass = p N0 y := by
    unfold Erdos1135.Tao.syracuseNoHitWindowProb
    rw [Erdos1135.Tao.pmfProb_oddLogWindowPMF, p_eq_logFinsetProb]
    rfl
  linarith

/-- If `y ≥ 2^{10000}`, the mass of the window is positive. -/
lemma mass_pos (y : ℝ) (hy : (2:ℝ) ^ (10000:ℕ) ≤ y) :
    0 < Erdos1135.Tao.logFinsetMass (Erdos1135.Tao.oddLogWindow (Erdos1135.Tao.taoNyLo y)
      (Erdos1135.Tao.taoNyHi y Erdos1135.Tao.taoAlpha)) := by
  have hZ : Erdos1135.Tao.logFinsetMass (Erdos1135.Tao.oddLogWindow (Erdos1135.Tao.taoNyLo y)
      (Erdos1135.Tao.taoNyHi y Erdos1135.Tao.taoAlpha)) = Zw y := by
    unfold Zw Erdos1135.Tao.logFinsetMass
    rw [W_eq_taoNy y]
    unfold Erdos1135.Tao.taoNyOddWindow
    exact Finset.sum_congr rfl fun N _ => (wt_eq_logNatWeight N).symm
  rw [hZ]
  have hgap := dyadic_log_gap hy
  have hZw := dyadic_Zw_ge y
  have h2 : (2:ℝ) ≤ ((Nat.log 2 ⌊y ^ alpha⌋₊ - Nat.log 2 ⌈y⌉₊ - 1 : ℕ) : ℝ) := by
    have : 2 ≤ Nat.log 2 ⌊y ^ alpha⌋₊ - Nat.log 2 ⌈y⌉₊ - 1 := by omega
    exact_mod_cast this
  linarith

/-- **One-step recursion (unconditional)**: from Mazur's formalization of the one step of §3 of Tao's paper and the
error bundle derived from Rhin's phase gap. -/
theorem stepHyp_nd : ∃ C c X : ℝ, 0 ≤ C ∧ 0 < c ∧ StepHyp C c X := by
  obtain ⟨cg, hPhase⟩ := Erdos1135.ND.existsPhaseGapRhin
  have hd : (0:ℝ) < 1 / 40 := by norm_num
  have hd20 : (1 / 40 : ℝ) < 1 / 20 := by norm_num
  have hdk : (1 / 40 : ℝ) < 1 / (2 * (143 / 10 : ℝ)) := by norm_num
  obtain ⟨B0, -, -, -, -, hBounds⟩ :=
    Erdos1135.ND.exists_ndA5ReferenceSection3SplitRealRatePacket hPhase hd hd20 hdk
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp
    (Erdos1135.ND.eventually_ndA5ReferenceSection3StepError_le_real_log_power B0 hd hd20)
  refine ⟨960084, 1 / 40, max X0 ((2:ℝ) ^ (10000:ℕ)), by norm_num, hd, ?_⟩
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

end Collatz
