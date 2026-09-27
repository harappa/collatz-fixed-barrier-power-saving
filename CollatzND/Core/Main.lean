import CollatzND.Core.Bridge
import Erdos1135.ND.Discrepancy.A5ReferenceND31Main

/-!
# The part of `CollatzND.Main` used by the main theorem (Theorem 1.1 of the paper)

The declarations of `CollatzND.Main` that lie in the dependency closure of the main theorem
`Collatz.nd_collatz_uniform_explicit` (and of `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`), moved
here without changing their statements or proofs (2026-09-26: separation of the minimal closure of the main theorem
from earlier development paths). The remaining declarations stay in `CollatzND.Main` in the source repository.
-/

namespace Collatz

open Classical

lemma orbitMin_gt_iff (N0 N : ℕ) : N0 < Erdos1135.ND.syracuseOrbitMin N ↔ SyrMinGT N0 N := by
  unfold Erdos1135.ND.syracuseOrbitMin Erdos1135.ND.syracuseOrbitValues SyrMinGT
  rw [Syr_eq_syracuse]
  constructor
  · intro h k; exact lt_of_lt_of_le h (Nat.sInf_le ⟨k, rfl⟩)
  · intro h
    have hne : (Set.range fun m => Erdos1135.Tao.syracuse^[m] N).Nonempty := ⟨_, 0, rfl⟩
    obtain ⟨k, hk⟩ := Nat.sInf_mem hne
    rw [← hk]; exact h k

/-- The bad probability under the logarithmically uniform measure on the top window equals `p`. -/
lemma logBad_eq_p (N0 : ℕ) (y : ℝ)
    (hmass : 0 < Erdos1135.Tao.logFinsetMass (Erdos1135.ND.oddBlock y)) :
    Erdos1135.Tao.pmfProb (Erdos1135.ND.logOddBlockPMF y hmass)
      {N | N0 < Erdos1135.ND.syracuseOrbitMin N.1} = p N0 y := by
  have hset : {N : {n // n ∈ Erdos1135.ND.oddBlock y} | N0 < Erdos1135.ND.syracuseOrbitMin N.1} =
      {N : {n // n ∈ Erdos1135.ND.oddBlock y} | (N : ℕ) ∈ Erdos1135.Tao.syracuseNoHitAtMost N0} := by
    ext N
    simp only [Set.mem_setOf_eq]
    rw [orbitMin_gt_iff, syrMinGT_iff_noHit]
  rw [hset]
  unfold Erdos1135.ND.logOddBlockPMF
  rw [Erdos1135.Tao.pmfProb_logFinsetPMF, p_eq_logFinsetProb]
  rfl

/-- The count of the odd bad set is at most the count `E` (`E N0 R = #{M < R : Col_min(M) > N0}`, cf. `E(X, N_0)` in Section 2 of the paper). -/
lemma natCount_le_E (N0 R : ℕ) :
    Erdos1135.Terras.natCount (Erdos1135.ND.oddSyracuseBadSet N0) R ≤ E N0 R := by
  unfold Erdos1135.Terras.natCount E
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro N hN
  rw [Finset.mem_filter] at hN ⊢
  refine ⟨hN.1, ?_⟩
  obtain ⟨_, hodd, hnh⟩ := hN.2
  exact exc_of_syr (Nat.odd_iff.mp hodd) ((syrMinGT_iff_noHit N0 N).mpr hnh)

lemma boundary_zero (X : ℝ) : Erdos1135.Tao.taoSection3AmbientBoundary X 0 = X := by
  simp [Erdos1135.Tao.taoSection3AmbientBoundary]

end Collatz
