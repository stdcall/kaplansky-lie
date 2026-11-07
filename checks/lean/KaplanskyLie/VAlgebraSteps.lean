import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Bounded steps of the theory of `V`-algebras

Chapter I, § 8, pp. 80–86.

* Theorem 88, step (b) (`step:rank-one-no-divisors`, formula (14),
  `eq:rank-one-congruence`): `rank_one_congruence`: for `(p + 1)/2 ≤ j ≤ p - 2` and
  `1 ≤ r ≤ p - j + 2` one never has `r ≡ 1 - 2 j (mod p)`; `rank_one_r_lt_p`: such
  `r` is not divisible by `p`, as theorem 58 requires (this is where `p > 3` enters).
* Theorem 90, step (a) (`step:isotropic-difference-root`, formulas (15), (16),
  `eq:isotropic-induction`, `eq:isotropic-induction-step`): `eq15`; `descent`: the
  conclusion `u = 0`, which needs all of `i = p - 1, p - 2, …, 1`, not only `i = p - 1`.
* Theorem 90, step (d) (`step:isotropic-not-integer`): `step_d`: for an isotropic `α`
  and `(h_α, h_β) = i (h_β, h_β)`, one has
  `(h_γ, h_γ) = (h_β, h_β) (1 + 2 i j)` for `γ = β + j α`, which is `0` for
  `j ≡ -1/(2 i)`; `step_d_printed_false`: the printed `j ≡ 1 - 2 i` fails at `p = 5`, `i = 1`.
* Theorems 93, 94, 96 (`th:root-sum-product`, `th:root-string-mod-p`,
  `th:root-string-length-char-p`): `chain_products`: the bare computation that replaces
  the argument of §5 in characteristic `p`.  For an unbroken `α`-string of `t < p`
  one-dimensional root spaces, with `e_i R_a = p_i e_(i+1)`, `e_(i+1) R_x = q_i e_i` and
  `[R_a, R_x] = R_h` acting on `e_i` as `λ + i`, one has
  `p_i q_i = (i + 1) (λ + i / 2)`; the top of the string gives `2 λ = -(t - 1)`, and then
  `p_i, q_i ≠ 0` inside the string.  At `p = 5` the words "дословно повторить" of p. 86 need
  this recursion: `s ≡ r + 2 m` and `s ≤ m + r` alone do not exclude `(m, r, s) = (2, 2, 1)`
  and `(3, 1, 2)`; see `checks/sage/chapter-1d.py`.

Notation.  `K` is a field, `V` a `K`-module, `A`, `X`, `Hα` linear maps: `A = R_a`, `X = R_x`,
`Hα = R_(h_α)`; the book's `u A` is `A u`.  The hypotheses of `eq15` are the facts of step (a):
`a x = h_α` gives `X (A v) = A (X v) + Hα v`; `a h_α = 0` gives that `A` and `Hα` commute.

Not covered: the passage from `V`-algebras to these sequences; theorem 92 (the bound `t ≤ 4`);
the steps (c), (d)–(j) of theorem 88 other than the arithmetic of (b).  They are checked
on examples in `checks/sage/chapter-1d.py`.
-/

namespace KaplanskyLie.VAlgebraSteps

/-- Step (b): for `(p + 1)/2 ≤ j ≤ p - 2`, `r ≤ p - j + 2` is less than `p`. -/
theorem rank_one_r_lt_p {p j r : ℕ} (hp : 3 < p) (hj : p + 1 ≤ 2 * j)
    (hr : r + j ≤ p + 2) : r < p := by
  omega

/-- Step (b): `r ≡ 1 - 2 j (mod p)`, i.e. `p ∣ r + 2 j - 1`, is impossible. -/
theorem rank_one_congruence {p j r : ℕ} (hj1 : p + 1 ≤ 2 * j) (hj2 : j + 2 ≤ p) (hr1 : 1 ≤ r)
    (hr : r + j ≤ p + 2) : ¬ p ∣ r + 2 * j - 1 := by
  rintro ⟨c, hc⟩
  have h1 : p < r + 2 * j - 1 := by omega
  have h2 : r + 2 * j - 1 < 2 * p := by omega
  rcases c with _ | _ | c
  · omega
  · omega
  · have : p * (c + 1 + 1) = p * c + 2 * p := by ring
    omega

section induction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {A X Hα : V →ₗ[K] V} {u : V} {b : K}

theorem h_on_powers (hAH : ∀ v, Hα (A v) = A (Hα v)) (hH : Hα u = b • u) (i : ℕ) :
    Hα (A^[i] u) = b • A^[i] u := by
  induction i with
  | zero => simpa using hH
  | succ i ih => rw [Function.iterate_succ_apply', hAH, ih, map_smul]

/-- Formula (15): `u R_a^(i+1) R_x = (i + 1) β(h_α) u R_a^i`. -/
theorem eq15 (hAX : ∀ v, X (A v) = A (X v) + Hα v) (hAH : ∀ v, Hα (A v) = A (Hα v))
    (hX : X u = 0) (hH : Hα u = b • u) (i : ℕ) :
    X (A^[i + 1] u) = (((i + 1 : ℕ) : K) * b) • A^[i] u := by
  induction i with
  | zero =>
    simp only [Function.iterate_one, Function.iterate_zero, id_eq, hAX, hX, map_zero, zero_add, hH]
    simp
  | succ i ih =>
    rw [Function.iterate_succ_apply' A (i + 1), hAX, ih, map_smul, h_on_powers hAH hH (i + 1),
      ← Function.iterate_succ_apply' A i, ← add_smul]
    congr 1
    push_cast
    ring

/-- Step (a), the conclusion: if `β(h_α) ≠ 0` and `u R_a^(p-1) = 0`, then `u = 0`.  The formula
is used for all `i = p - 1, p - 2, …, 1`. -/
theorem descent {p : ℕ} [CharP K p] (hAX : ∀ v, X (A v) = A (X v) + Hα v)
    (hAH : ∀ v, Hα (A v) = A (Hα v)) (hX : X u = 0) (hH : Hα u = b • u) (hb : b ≠ 0)
    (hp : 0 < p) (htop : A^[p - 1] u = 0) : u = 0 := by
  have key : ∀ i, i ≤ p - 1 → A^[i] u = 0 → u = 0 := by
    intro i
    induction i with
    | zero =>
      intro _ h
      simpa using h
    | succ i ih =>
      intro hi h
      apply ih (by omega)
      have h1 := eq15 hAX hAH hX hH i
      rw [h, map_zero] at h1
      have hne : ((i + 1 : ℕ) : K) * b ≠ 0 := by
        refine mul_ne_zero ?_ hb
        intro h0
        have hd := (CharP.cast_eq_zero_iff K p _).mp h0
        have := Nat.le_of_dvd (Nat.succ_pos _) hd
        omega
      have h2 := inv_smul_smul₀ hne (A^[i] u)
      rw [← h1, smul_zero] at h2
      exact h2.symm
  exact key (p - 1) le_rfl htop

end induction

/-- Step (d): `(h_γ, h_γ) = (h_β, h_β) (1 + 2 i j)` for `γ = β + j α`, `(h_α, h_α) = 0`,
`(h_α, h_β) = i (h_β, h_β)`; the corrected `j = -1/(2 i)` makes it `0`. -/
theorem step_d {K : Type*} [Field K] (bb ab aa i j : K) (haa : aa = 0) (hab : ab = i * bb)
    (hj : 2 * i * j = -1) : bb + 2 * j * ab + j ^ 2 * aa = 0 := by
  rw [haa, hab]
  linear_combination bb * hj

/-- The printed value `j ≡ 1 - 2 i` fails: `p = 5`, `i = 1`. -/
theorem step_d_printed_false : (1 + 2 * (1 : ZMod 5) * (1 - 2 * 1) : ZMod 5) ≠ 0 := by
  decide

/-- The corrected value exists: for `i ≠ 0`, `2 ≠ 0`, `j = -(2 i)⁻¹` is nonzero. -/
theorem step_d_exists {K : Type*} [Field K] (i : K) (hi : i ≠ 0) (h2 : (2 : K) ≠ 0) :
    ∃ j : K, j ≠ 0 ∧ 2 * i * j = -1 := by
  have h : 2 * i ≠ 0 := mul_ne_zero h2 hi
  refine ⟨-(2 * i)⁻¹, neg_ne_zero.mpr (inv_ne_zero h), ?_⟩
  rw [mul_neg, mul_inv_cancel₀ h]

section chain

variable {K : Type*} [Field K]

/-- `p_i q_i = (i + 1) λ + C(i + 1, 2)` from the commutator relation. -/
theorem chain_formula {P Q : ℕ → K} {lam : K} (h0 : P 0 * Q 0 = lam)
    (hrec : ∀ i, P (i + 1) * Q (i + 1) - P i * Q i = lam + ((i + 1 : ℕ) : K)) (i : ℕ) :
    2 * (P i * Q i) = ((i + 1 : ℕ) : K) * (2 * lam + (i : K)) := by
  induction i with
  | zero =>
    rw [h0]
    simp
  | succ i ih =>
    have h := hrec i
    push_cast at h ih ⊢
    linear_combination ih + 2 * h

/-- Theorems 93, 94, 96: the top of the string gives `2 λ = -(t - 1)`, and all products inside
the string are nonzero, when the string is shorter than `p`. -/
theorem chain_products {p : ℕ} [CharP K p] {P Q : ℕ → K} {lam : K} (h0 : P 0 * Q 0 = lam)
    (hrec : ∀ i, P (i + 1) * Q (i + 1) - P i * Q i = lam + ((i + 1 : ℕ) : K))
    {t : ℕ} (ht0 : 0 < t) (htp : t < p) (htop : P (t - 1) * Q (t - 1) = 0) :
    2 * lam = -((t : K) - 1) ∧ ∀ i, i + 1 < t → P i ≠ 0 ∧ Q i ≠ 0 := by
  have hne : ∀ n : ℕ, 0 < n → n < p → (n : K) ≠ 0 := by
    intro n h1 h2 h0
    have hd := (CharP.cast_eq_zero_iff K p n).mp h0
    have := Nat.le_of_dvd h1 hd
    omega
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at htop
  have htopf := chain_formula h0 hrec s
  rw [htop, mul_zero] at htopf
  have hlam : 2 * lam + (s : K) = 0 :=
    (mul_eq_zero.mp htopf.symm).resolve_left (hne _ (by omega) htp)
  refine ⟨?_, ?_⟩
  · push_cast
    linear_combination hlam
  · intro i hi
    have hf := chain_formula h0 hrec i
    have e : (2 : K) * (P i * Q i) = -(((i + 1 : ℕ) : K) * ((s - i : ℕ) : K)) := by
      rw [hf]
      have hc : ((s - i : ℕ) : K) = (s : K) - (i : K) := by
        rw [Nat.cast_sub (by omega)]
      rw [hc]
      linear_combination ((i + 1 : ℕ) : K) * hlam
    have hprod : P i * Q i ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at e
      have h1 := hne (i + 1) (by omega) (by omega)
      have h2 := hne (s - i) (by omega) (by omega)
      exact neg_ne_zero.mpr (mul_ne_zero h1 h2) e.symm
    exact ⟨left_ne_zero_of_mul hprod, right_ne_zero_of_mul hprod⟩

end chain

end KaplanskyLie.VAlgebraSteps

#print axioms KaplanskyLie.VAlgebraSteps.rank_one_r_lt_p
#print axioms KaplanskyLie.VAlgebraSteps.rank_one_congruence
#print axioms KaplanskyLie.VAlgebraSteps.h_on_powers
#print axioms KaplanskyLie.VAlgebraSteps.eq15
#print axioms KaplanskyLie.VAlgebraSteps.descent
#print axioms KaplanskyLie.VAlgebraSteps.step_d
#print axioms KaplanskyLie.VAlgebraSteps.step_d_printed_false
#print axioms KaplanskyLie.VAlgebraSteps.step_d_exists
#print axioms KaplanskyLie.VAlgebraSteps.chain_formula
#print axioms KaplanskyLie.VAlgebraSteps.chain_products
