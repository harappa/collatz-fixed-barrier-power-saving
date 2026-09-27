import CollatzND.Core.Explicit

set_option pp.explicit true in
#check @Collatz.nd_collatz_uniform_explicit
set_option pp.explicit true in
#check @Collatz.nd_collatz_uniform
set_option pp.all true in
#print Collatz.col
#print Collatz.tstarExponent
#print Collatz.cB
#print FirstPassageLinearTransport.FixedBarrier.fbFixedRate
#print axioms Collatz.nd_collatz_uniform_explicit
#print axioms Collatz.nd_collatz_uniform
#print axioms Collatz.tstarExponent_eq
#print axioms Collatz.tstarExponent_pos
#print axioms Collatz.fixedBarrier_failure_count_explicit
#print axioms FirstPassageLinearTransport.FixedBarrier.fixedBarrier_failure_count
#print axioms FirstPassageLinearTransport.FixedBarrier.fixedBarrier_failure_count_rate
set_option pp.explicit true in
#check @FirstPassageLinearTransport.FixedBarrier.fixedBarrier_failure_count_rate
set_option pp.all true in
#print FirstPassageLinearTransport.shortcut

-- sanity: col agrees with the usual 3x+1 map
example : Collatz.col 7 = 22 := by decide
example : Collatz.col 22 = 11 := by decide
example : Collatz.col 1 = 4 := by decide
example : FirstPassageLinearTransport.shortcut 7 = 11 := by decide

-- ColMinGT meaning: minimum over the whole orbit incl. m = 0
example (N0 N : ℕ) : (∀ m, N0 < Collatz.col^[m] N) → N0 < N := fun h => h 0

-- instantiate the statement at concrete values to see it is not vacuous in the hypotheses
open Classical in
example : ∃ K c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
  (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < Collatz.col^[m] N)).card : ℝ) ≤ K * (N0 : ℝ) ^ (-c') * X :=
  Collatz.nd_collatz_uniform

-- Decidable instance used in the statement
set_option pp.explicit true in
#check (Collatz.nd_collatz_uniform)
