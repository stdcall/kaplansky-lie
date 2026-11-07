import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The Leibniz formula and the `p`-th power of a derivation

Chapter I, § 7, pp. 67–68: theorem 73 (`th:derivation-power-p`) and formula (11)
(`eq:leibniz-power`): if `D` is a derivation of an algebra `A` of characteristic
`p`, then `D^p` is a derivation.

Notation.  `A` is any (not necessarily associative) ring, as in the book's
"любая алгебра"; only the additive group and the product are used, so scalars
play no part.  The book writes operators on the right, `x D`; here `D x`, and
`D^n` is the iterate `D^[n]`.  "Characteristic `p`" is the hypothesis
`∀ a, p • a = 0` for a prime `p`.

* `IsDerivation`: additive with `D (x y) = D x · y + x · D y`.
* `iterate_add`: `D^n` is additive.
* `leibniz_iterate`: `(x y) D^n = Σ_i C(n, i) (x D^(n-i)) (y D^i)`: formula (11)
  for every `n`, in any characteristic.
* `prime_dvd_choose`: `p ∣ C(p, i)` for `0 < i < p`.
* `derivation_power_p`: theorem 73.
* `leibniz_power_p`: the conclusion of the proof, `(x y) D^p = x D^p · y + x · y D^p`.

Not covered: the definition of restricted algebras and (12); examples are checked in
`checks/sage/chapter-1d.py`.
-/

namespace KaplanskyLie.DerivationPower

open Finset

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- A derivation, in the book's sense, of a not necessarily associative ring. -/
structure IsDerivation (D : A → A) : Prop where
  map_add : ∀ x y, D (x + y) = D x + D y
  leibniz : ∀ x y, D (x * y) = D x * y + x * D y

/-- The iterates of an additive map are additive. -/
theorem iterate_add {D : A → A} (hD : ∀ x y, D (x + y) = D x + D y) (n : ℕ) (x y : A) :
    D^[n] (x + y) = D^[n] x + D^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, hD]

theorem iterate_zero_of_add {D : A → A} (hD : ∀ x y, D (x + y) = D x + D y) (n : ℕ) :
    D^[n] 0 = 0 := by
  have h := iterate_add hD n 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem map_nsmul_of_add {D : A → A} (hD : ∀ x y, D (x + y) = D x + D y) (k : ℕ) (x : A) :
    D (k • x) = k • D x := by
  have h0 : D 0 = 0 := iterate_zero_of_add hD 1
  induction k with
  | zero => simp [h0]
  | succ k ih => rw [succ_nsmul, hD, ih, succ_nsmul]

theorem map_sum_of_add {D : A → A} (hD : ∀ x y, D (x + y) = D x + D y) {ι : Type*}
    (s : Finset ι) (f : ι → A) : D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i) := by
  classical
  have h0 : D 0 = 0 := iterate_zero_of_add hD 1
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, hD, ih]

/-- The Leibniz formula on the antidiagonal. -/
theorem leibniz_antidiagonal {D : A → A} (hD : IsDerivation D) (n : ℕ) (x y : A) :
    D^[n] (x * y) =
      ∑ ij ∈ antidiagonal n, (n.choose ij.1) • (D^[ij.1] x * D^[ij.2] y) := by
  induction n with
  | zero => simp [one_nsmul]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_sum_of_add hD.map_add,
      Finset.sum_antidiagonal_choose_succ_nsmul
        (fun i j => D^[i] x * D^[j] y) n]
    have key : ∀ ij ∈ antidiagonal n,
        D ((n.choose ij.1) • (D^[ij.1] x * D^[ij.2] y)) =
          (n.choose ij.1) • (D^[ij.1 + 1] x * D^[ij.2] y) +
            (n.choose ij.1) • (D^[ij.1] x * D^[ij.2 + 1] y) := by
      intro ij _
      rw [map_nsmul_of_add hD.map_add, hD.leibniz, nsmul_add,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [sum_congr rfl key, sum_add_distrib, add_comm]
    congr 1
    refine sum_congr rfl fun ij hij => ?_
    rw [← Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]

/-- Formula (11) for every `n`: `(x y) D^n = Σ_i C(n, i) (x D^(n-i)) (y D^i)`. -/
theorem leibniz_iterate {D : A → A} (hD : IsDerivation D) (n : ℕ) (x y : A) :
    D^[n] (x * y) =
      ∑ i ∈ range (n + 1), (n.choose i) • (D^[n - i] x * D^[i] y) := by
  rw [leibniz_antidiagonal hD,
    ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  simp only [Prod.swap_prod_mk, Nat.choose_symm hi']

/-- A prime does not divide `k!` for `k < p`. -/
theorem not_dvd_factorial {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k < p) : ¬ p ∣ k.factorial := by
  induction k with
  | zero =>
    rw [Nat.factorial_zero]
    exact hp.one_lt.ne' ∘ Nat.dvd_one.mp
  | succ k ih =>
    rw [Nat.factorial_succ]
    intro h
    rcases (hp.dvd_mul).mp h with h | h
    · exact absurd (Nat.le_of_dvd (Nat.succ_pos k) h) (by omega)
    · exact ih (by omega) h

/-- `p ∣ C(p, i)` for `0 < i < p`. -/
theorem prime_dvd_choose {p i : ℕ} (hp : p.Prime) (h0 : 0 < i) (hi : i < p) :
    p ∣ p.choose i := by
  have h := Nat.choose_mul_factorial_mul_factorial hi.le
  have hd : p ∣ p.choose i * i.factorial * (p - i).factorial := by
    rw [h]
    exact Nat.dvd_factorial hp.pos le_rfl
  rcases (hp.dvd_mul).mp hd with hd | hd
  · rcases (hp.dvd_mul).mp hd with hd | hd
    · exact hd
    · exact absurd hd (not_dvd_factorial hp hi)
  · exact absurd hd (not_dvd_factorial hp (by omega))

/-- The proof of theorem 73: the middle terms of (11) vanish for `n = p`. -/
theorem leibniz_power_p {p : ℕ} (hp : p.Prime) (hchar : ∀ a : A, p • a = 0) {D : A → A}
    (hD : IsDerivation D) (x y : A) :
    D^[p] (x * y) = D^[p] x * y + x * D^[p] y := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  rw [leibniz_iterate hD, sum_range_succ, sum_range_succ']
  have hmid : ∑ k ∈ range q, ((q + 1).choose (k + 1)) •
      (D^[q + 1 - (k + 1)] x * D^[k + 1] y) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    obtain ⟨c, hc⟩ := prime_dvd_choose hp (Nat.succ_pos k) (by have := mem_range.mp hk; omega)
    rw [hc, mul_nsmul', hchar]
  rw [hmid]
  simp [one_nsmul]

/-- Theorem 73: `D^p` is a derivation. -/
theorem derivation_power_p {p : ℕ} (hp : p.Prime) (hchar : ∀ a : A, p • a = 0) {D : A → A}
    (hD : IsDerivation D) : IsDerivation (D^[p]) :=
  ⟨iterate_add hD.map_add p, leibniz_power_p hp hchar hD⟩

end KaplanskyLie.DerivationPower

#print axioms KaplanskyLie.DerivationPower.iterate_add
#print axioms KaplanskyLie.DerivationPower.leibniz_antidiagonal
#print axioms KaplanskyLie.DerivationPower.leibniz_iterate
#print axioms KaplanskyLie.DerivationPower.not_dvd_factorial
#print axioms KaplanskyLie.DerivationPower.prime_dvd_choose
#print axioms KaplanskyLie.DerivationPower.leibniz_power_p
#print axioms KaplanskyLie.DerivationPower.derivation_power_p
