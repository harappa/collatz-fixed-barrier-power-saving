import CollatzProof.Core.Recursion

/-!
# The part of `CollatzProof.Syr` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzProof.Syr` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzProof.Syr` in the source repository.
-/

namespace Collatz

/-- The Syracuse map: the largest odd divisor of `3N+1`. -/
def Syr (N : ℕ) : ℕ := (3 * N + 1) / 2 ^ ((3 * N + 1).factorization 2)

lemma syr_decomp (N : ℕ) : 2 ^ ((3 * N + 1).factorization 2) * Syr N = 3 * N + 1 :=
  Nat.ordProj_mul_ordCompl_eq_self _ _

lemma syr_odd (N : ℕ) : Syr N % 2 = 1 := by
  have h := Nat.coprime_ordCompl (n := 3 * N + 1) Nat.prime_two (by omega)
  unfold Syr
  rcases Nat.mod_two_eq_zero_or_one ((3 * N + 1) / 2 ^ (3 * N + 1).factorization 2) with h0 | h1
  · exfalso
    have : 2 ∣ (3 * N + 1) / 2 ^ (3 * N + 1).factorization 2 := Nat.dvd_of_mod_eq_zero h0
    have := Nat.Coprime.eq_one_of_dvd h this
    omega
  · exact h1

lemma syr_val_pos {N : ℕ} (hN : N % 2 = 1) : 0 < (3 * N + 1).factorization 2 :=
  Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) (by omega)

lemma syr_iter_odd {N : ℕ} (hN : N % 2 = 1) : ∀ k, Syr^[k] N % 2 = 1 := by
  intro k
  induction k with
  | zero => simpa using hN
  | succ k _ => rw [Function.iterate_succ_apply']; exact syr_odd _

/-- Applying `T` to `2^r m`. -/
lemma T_two_pow_mul_succ (r m : ℕ) : T (2 ^ (r + 1) * m) = 2 ^ r * m := by
  have e : 2 ^ (r + 1) * m = 2 * (2 ^ r * m) := by rw [pow_succ]; ring
  rw [e]
  have h2 := two_mul_T_of_even (m := 2 * (2 ^ r * m)) (by omega)
  omega

lemma T_odd (m : ℕ) (hm : m % 2 = 1) :
    T m = 2 ^ ((3 * m + 1).factorization 2 - 1) * Syr m := by
  have hd := syr_decomp m
  have hv := syr_val_pos hm
  have h2 := two_mul_T_of_odd hm
  set ν := (3 * m + 1).factorization 2 with hν
  have e : (2:ℕ) ^ ν = 2 * 2 ^ (ν - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [e] at hd
  have : 2 * T m = 2 * (2 ^ (ν - 1) * Syr m) := by
    calc 2 * T m = 3 * m + 1 := h2
      _ = 2 * 2 ^ (ν - 1) * Syr m := hd.symm
      _ = 2 * (2 ^ (ν - 1) * Syr m) := by ring
  omega

/-- For odd `N`, every value of the `T`-orbit of `N` has the form `2^r Syr^k(N)`. -/
theorem T_orbit_form {N : ℕ} (hN : N % 2 = 1) :
    ∀ i, ∃ k r, T^[i] N = 2 ^ r * Syr^[k] N := by
  intro i
  induction i with
  | zero => exact ⟨0, 0, by simp⟩
  | succ i ih =>
    obtain ⟨k, r, h⟩ := ih
    rw [Function.iterate_succ_apply', h]
    rcases r with _ | r
    · refine ⟨k + 1, (3 * Syr^[k] N + 1).factorization 2 - 1, ?_⟩
      rw [pow_zero, one_mul, T_odd _ (syr_iter_odd hN k), Function.iterate_succ_apply']
    · exact ⟨k, r, T_two_pow_mul_succ r _⟩

/-- For odd `N`, `Syr_min(N) > N0` implies `Exc N0 N`. -/
theorem exc_of_syr {N0 N : ℕ} (hN : N % 2 = 1) (h : ∀ k, N0 < Syr^[k] N) : Exc N0 N := by
  intro i
  obtain ⟨k, r, hi⟩ := T_orbit_form hN i
  rw [hi]
  have := h k
  have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  nlinarith

end Collatz
