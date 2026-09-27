import CollatzND.Core.Col

/-!
# Specification tests for the statement of the main theorem (Theorem 1.1 of the paper)

Theorem 1.1 of the paper is the main theorem (a power saving uniform in `x`). We check on small values that `col`,
`∀ m, N0 < col^[m] N` and `(Finset.Icc 1 X).filter … |>.card`, as they appear in the statement of
`nd_collatz_uniform`, have the intended meaning. The inequality of the theorem itself cannot serve as a check (for
`N0 ≥ 1` the set is empty in every range small enough to check), so we check the definitions instead. Only `decide`
and `rfl` are used; `native_decide` is not.
Values from an external brute force (Python): `Atrunc 1 30 10 = 17`, `Atrunc 4 50 15 = 21`, `Atrunc 10 60 8 = 28`.
-/

namespace Collatz

set_option maxRecDepth 100000

/-- Count with the truncated predicate (`∀ m < T`). Used to check the set definitions (`Icc`, `filter`, `card`). -/
def Atrunc (N0 X T : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun N => ∀ m < T, N0 < col^[m] N)).card

-- 1. `col` is the standard Collatz map (n/2 for even n, 3n+1 for odd n)
example : col 27 = 82 := by decide
example : col 82 = 41 := by decide
example : col 1 = 4 := by decide
example : col 4 = 2 := by decide
example : col 0 = 0 := by decide

-- 2. Iteration includes `m = 0` (`col^[0] N = N`). The orbit of 27 reaches 1 after 111 steps; its maximum is 9232 (at step 77)
example : col^[0] 27 = 27 := rfl
example : col^[77] 27 = 9232 := by decide
example : col^[111] 27 = 1 := by decide

-- 3. The set predicate is not vacuous: the truncated predicate can hold
example : ∀ m < 20, 5 < col^[m] 27 := by decide

-- 4. The truncated counts agree with the external brute force (`Icc 1 X` includes both endpoints; `<` is strict)
example : Atrunc 1 30 10 = 17 := by decide
example : Atrunc 4 50 15 = 21 := by decide
example : Atrunc 10 60 8 = 28 := by decide

-- 5. `Col_min(27) > 1` is false (the orbit hits 1 at step 111)
example : ¬ ColMinGT 1 27 := fun h => by
  have h1 : col^[111] 27 = 1 := by decide
  have := h 111
  omega

/-- If `col n = 0` then `n = 0` (stated in the contrapositive form `0 < n → 0 < col n`). -/
lemma col_pos {n : ℕ} (hn : 0 < n) : 0 < col n := by
  unfold col; split_ifs <;> omega

/-- The orbit of a positive number stays positive. -/
lemma iterate_col_pos {n : ℕ} (hn : 0 < n) : ∀ m, 0 < col^[m] n := by
  intro m
  induction m with
  | zero => simpa using hn
  | succ m ih => rw [Function.iterate_succ_apply']; exact col_pos ih

open Classical in
-- 6. For `N0 = 0` the set is all of `[1, X]` (a positive check of the meaning of `Icc`, `filter`, `card`)
example : A 0 30 = 30 := by
  have h : ∀ N ∈ Finset.Icc 1 30, ColMinGT 0 N := fun N hN =>
    iterate_col_pos (by have := (Finset.mem_Icc.mp hN).1; omega)
  unfold A
  rw [Finset.filter_true_of_mem h]
  simp

open Classical in
-- 7. `N0 = 1`, `X = 30`: every orbit reaches 1, so the set is empty (`∀ N ≤ 30, ∃ m ≤ 111, col^[m] N ≤ 1`)
example : A 1 30 = 0 := by
  unfold A
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro N hN hmin
  have hN' := Finset.mem_Icc.mp hN
  have hhit : ∀ N ∈ Finset.Icc 1 30, ∃ m ∈ Finset.range 112, col^[m] N ≤ 1 := by decide
  obtain ⟨m, -, hm⟩ := hhit N hN
  have := hmin m
  omega

end Collatz
