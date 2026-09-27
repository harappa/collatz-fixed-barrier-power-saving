import CollatzProof.Core.Defs

/-!
# The part of `CollatzProof.Recursion` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzProof.Recursion` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzProof.Recursion` in the source repository.
-/

namespace Collatz

open Classical

/-- `Col_min(M) > N0` (every value of the orbit is larger than `N0`). -/
def Exc (N0 M : ℕ) : Prop := ∀ i, N0 < T^[i] M

/-- `E N0 R = #{M < R : Col_min(M) > N0}`. -/
noncomputable def E (N0 R : ℕ) : ℕ := ((Finset.range R).filter (Exc N0)).card

lemma E_mono (N0 : ℕ) {R R' : ℕ} (h : R ≤ R') : E N0 R ≤ E N0 R' := by
  unfold E
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

end Collatz
