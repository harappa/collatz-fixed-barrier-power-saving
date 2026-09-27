import CollatzND.Core.Main

/-!
# The part of `CollatzND.Col` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzND.Col` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzND.Col` in the source repository.
-/

namespace Collatz

open Classical

/-- The usual Collatz map. -/
def col (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `Col_min(N) > N0` (every value of the Collatz orbit of `N` exceeds `N0`). -/
def ColMinGT (N0 N : ℕ) : Prop := ∀ m, N0 < col^[m] N

lemma col_two_mul (s : ℕ) : col (2 * s) = s := by
  unfold col; rw [if_pos (by omega)]; omega

lemma col_halve (j s : ℕ) : col^[j] (2 ^ j * s) = s := by
  induction j generalizing s with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, show 2 ^ (j + 1) * s = 2 * (2 ^ j * s) by ring, col_two_mul, ih]

lemma col_syr (n : ℕ) (hn : n % 2 = 1) : col^[(3 * n + 1).factorization 2 + 1] n = Syr n := by
  rw [Function.iterate_add_apply]
  have h1 : col^[1] n = 3 * n + 1 := by
    simp only [Function.iterate_one]; unfold col; rw [if_neg (by omega)]
  rw [h1]
  set v := (3 * n + 1).factorization 2
  have hd : 3 * n + 1 = 2 ^ v * Syr n := (syr_decomp n).symm
  rw [hd]
  exact col_halve v (Syr n)

lemma col_orbit_syr (N : ℕ) (hN : N % 2 = 1) : ∀ k, ∃ m, col^[m] N = Syr^[k] N := by
  intro k
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨((3 * Syr^[k] N + 1).factorization 2 + 1) + m, ?_⟩
    rw [Function.iterate_add_apply, hm, col_syr _ (syr_iter_odd hN k),
      Function.iterate_succ_apply']

lemma colMinGT_syr {N0 N : ℕ} (hN : N % 2 = 1) (h : ColMinGT N0 N) : SyrMinGT N0 N := by
  intro k
  obtain ⟨m, hm⟩ := col_orbit_syr N hN k
  rw [← hm]; exact h m

lemma colMinGT_half {N0 M : ℕ} (h : ColMinGT N0 (2 * M)) : ColMinGT N0 M := by
  intro m
  have := h (m + 1)
  rwa [Function.iterate_succ_apply, col_two_mul] at this

/-- `A(X) = #{1 ≤ N ≤ X : Col_min(N) > N0}`. -/
noncomputable def A (N0 X : ℕ) : ℕ := ((Finset.Icc 1 X).filter (ColMinGT N0)).card

lemma A_rec (N0 X : ℕ) :
    A N0 X ≤ Erdos1135.ND.natCountLE (Erdos1135.ND.oddSyracuseBadSet N0) X + A N0 (X / 2) := by
  unfold A
  set S := (Finset.Icc 1 X).filter (ColMinGT N0)
  rw [← Finset.card_filter_add_card_filter_not (s := S) (fun N => N % 2 = 1)]
  apply add_le_add
  · unfold Erdos1135.ND.natCountLE Erdos1135.Terras.natCount
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_le_card
    intro N hN
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨⟨h1, h2⟩, hC⟩, hodd⟩ := hN
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, Nat.odd_iff.mpr hodd, ?_⟩
    have := (syrMinGT_iff_noHit N0 N).mp (colMinGT_syr hodd hC)
    exact this
  · apply Finset.card_le_card_of_injOn (fun N => N / 2)
    · intro N hN
      simp only [S, Finset.coe_filter, Finset.mem_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hN ⊢
      obtain ⟨⟨⟨h1, h2⟩, hC⟩, hev⟩ := hN
      have hN2 : N = 2 * (N / 2) := by omega
      refine ⟨⟨by omega, Nat.div_le_div_right h2⟩, ?_⟩
      rw [hN2] at hC
      exact colMinGT_half hC
    · intro N1 hN1 N2 hN2 heq
      simp only [S, Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hN1 hN2
      simp only at heq
      omega

lemma natCountLE_small (N0 Y : ℕ) (hN0 : 1 ≤ N0) (hY : Y ≤ 1) :
    Erdos1135.ND.natCountLE (Erdos1135.ND.oddSyracuseBadSet N0) Y = 0 := by
  unfold Erdos1135.ND.natCountLE Erdos1135.Terras.natCount
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro N hN hbad
  rw [Finset.mem_range] at hN
  obtain ⟨hpos, -, hnh⟩ := hbad
  apply hnh
  exact ⟨0, by simp; omega⟩

lemma A_bound (N0 : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hO : ∀ Y : ℕ, (Erdos1135.ND.natCountLE (Erdos1135.ND.oddSyracuseBadSet N0) Y : ℝ) ≤ ε * Y) :
    ∀ X : ℕ, (A N0 X : ℝ) ≤ 2 * ε * X := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    rcases Nat.eq_zero_or_pos X with h0 | hpos
    · subst h0; simp [A]
    · have hrec := A_rec N0 X
      have hhalf := ih (X / 2) (Nat.div_lt_self hpos (by norm_num))
      have hc : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 := Nat.cast_div_le
      have hrec' : (A N0 X : ℝ) ≤
          (Erdos1135.ND.natCountLE (Erdos1135.ND.oddSyracuseBadSet N0) X : ℝ) + A N0 (X / 2) := by
        exact_mod_cast hrec
      nlinarith [hO X]

end Collatz
