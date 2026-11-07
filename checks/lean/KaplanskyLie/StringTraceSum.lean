import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The trace computation in theorem 32

Chapter I, § 3, the end of the proof of theorem 32, p. 39.  `S_x` is triangular with diagonal
`α, α + 1, ..., α + k`, and `Tr S_x = 0`.  The book concludes `α = -k/2` (printed `k/2`, a misprint
corrected in our text) and `f(x, x) = Tr S_x² = k (k + 1) (k + 2) / 12`.

* `sum_arith_eq_zero_iff`: `α + (α + 1) + ... + (α + k) = 0` if and only if `α = -k/2`.
* `sum_squares`: at `α = -k/2` the sum of squares is `k (k + 1) (k + 2) / 12`.
* `sum_squares_pos`: this is positive for `k ≥ 1`.
* `printed_alpha_not_trace_zero`: the printed `α = k/2` does not satisfy `Tr S_x = 0` for `k ≥ 1`.

Over `ℚ`: the numbers involved are rational, which is the book's point.  Not covered: everything
before this computation; explicit modules are in `checks/sage/chapter-1b.py`.
-/

namespace KaplanskyLie.StringTraceSum

open Finset

theorem sum_id (k : ℕ) : ∑ i ∈ range (k + 1), (i : ℚ) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

theorem sum_sq (k : ℕ) : ∑ i ∈ range (k + 1), (i : ℚ) ^ 2 = k * (k + 1) * (2 * k + 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

theorem sum_arith (α : ℚ) (k : ℕ) :
    ∑ i ∈ range (k + 1), (α + i) = (k + 1) * (α + k / 2) := by
  rw [sum_add_distrib, sum_id]
  simp only [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `Tr S_x = 0` if and only if `α = -k/2`. -/
theorem sum_arith_eq_zero_iff (α : ℚ) (k : ℕ) :
    ∑ i ∈ range (k + 1), (α + i) = 0 ↔ α = -(k / 2) := by
  rw [sum_arith]
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  constructor
  · intro h
    have := (mul_eq_zero.1 h).resolve_left hk
    linarith
  · intro h
    rw [h]
    ring

/-- `f(x, x) = k (k + 1) (k + 2) / 12`. -/
theorem sum_squares (k : ℕ) :
    ∑ i ∈ range (k + 1), (-((k : ℚ) / 2) + i) ^ 2 = (k : ℚ) * (k + 1) * (k + 2) / 12 := by
  have e : ∀ i : ℕ, (-((k : ℚ) / 2) + i) ^ 2 = (k : ℚ) ^ 2 / 4 - k * i + (i : ℚ) ^ 2 := by
    intro i
    ring
  simp only [e]
  rw [sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum, sum_id, sum_sq]
  simp only [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The sum is positive for `k ≥ 1`. -/
theorem sum_squares_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < ∑ i ∈ range (k + 1), (-((k : ℚ) / 2) + i) ^ 2 := by
  rw [sum_squares]
  have h0 : (0 : ℚ) < k := by exact_mod_cast hk
  have h1 : (0 : ℚ) < (k : ℚ) * (k + 1) * (k + 2) := by
    have h2 : (0 : ℚ) < (k : ℚ) + 1 := by linarith
    have h3 : (0 : ℚ) < (k : ℚ) + 2 := by linarith
    exact mul_pos (mul_pos h0 h2) h3
  exact div_pos h1 (by norm_num)

/-- The printed reading `α = k/2` does not give `Tr S_x = 0`. -/
theorem printed_alpha_not_trace_zero (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ range (k + 1), ((k : ℚ) / 2 + i) ≠ 0 := by
  intro h
  have := (sum_arith_eq_zero_iff _ _).1 h
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  linarith

end KaplanskyLie.StringTraceSum

#print axioms KaplanskyLie.StringTraceSum.sum_arith_eq_zero_iff
#print axioms KaplanskyLie.StringTraceSum.sum_squares
#print axioms KaplanskyLie.StringTraceSum.sum_squares_pos
#print axioms KaplanskyLie.StringTraceSum.printed_alpha_not_trace_zero
