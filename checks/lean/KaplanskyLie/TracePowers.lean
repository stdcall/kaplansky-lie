import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Traces of powers and sums of commutators

Chapter I, § 2, theorems 17 and 18, p. 28, and the invariance of the form `Tr(S_x S_y)`, p. 34.
A linear transformation of a finite-dimensional space over a field `K` of characteristic zero is
written as a square matrix `Z` over `K`; the book's action on the right plays no role, because
the statements are about the matrix ring.

* `isNilpotent_of_trace_pow`: theorem 17, if `Tr(Z^k) = 0` for every `k ≥ 1` then `Z` is
  nilpotent.  The book splits `V = V_1 ⊕ V_2` (`Z` nonsingular on `V_1`, nilpotent on `V_2`) and
  takes the trace of the polynomial relation of `Z` on `V_1`, whose constant term is not zero.
  Here the same splitting is reached through the projector onto `V_1`, written as a polynomial
  `E = a(Z) Z^(m+1)` in `Z` without constant term (Bezout for the factors `X^(m+1)` and `q` of
  the characteristic polynomial `X^m q`, `q(0) ≠ 0`): `Tr E = 0` by hypothesis, an idempotent of
  trace zero in characteristic zero is zero, so `V_1 = 0`.
* `pow_eq_sum_commutators`: the display of the proof of theorem 18,
  `Z^n = ∑ [A_i, Z^(n-1) B_i]` if `Z` commutes with all `A_i`.
* `isNilpotent_sum_commutators`: theorem 18.
* `trace_form_invariant`: `Tr((S_x S_y - S_y S_x) S_z) = Tr(S_x (S_y S_z - S_z S_y))`, p. 34.

Not covered: the characteristic hypothesis is not shown to be needed here (for `Z` the unit
`p × p` matrix in characteristic `p`, see `checks/sage/chapter-1a.py`); the theorems of § 2 using
these results.
-/

namespace KaplanskyLie.TracePowers

open Polynomial Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The trace of `f(Z) Z` is a combination of traces of positive powers of `Z`. -/
theorem trace_aeval_mul_X (Z : Matrix n n K) (h : ∀ k, 0 < k → (Z ^ k).trace = 0) (f : K[X]) :
    (aeval Z (f * X)).trace = 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_mul, map_add, Matrix.trace_add, hp, hq, add_zero]
  | monomial k c =>
      have : aeval Z (monomial k c * X) = c • Z ^ (k + 1) := by
        rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_succ, map_mul, aeval_C, map_pow, aeval_X,
          Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      rw [this, Matrix.trace_smul, h _ (Nat.succ_pos k), smul_zero]

/-- An idempotent matrix of trace zero over a field of characteristic zero is zero. -/
theorem eq_zero_of_idempotent_of_trace [CharZero K] (E : Matrix n n K) (hE : E * E = E)
    (hT : E.trace = 0) : E = 0 := by
  have hid : IsIdempotentElem (Matrix.toLin' E) := by
    show Matrix.toLin' E * Matrix.toLin' E = Matrix.toLin' E
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  have htr : LinearMap.trace K (n → K) (Matrix.toLin' E) = 0 := by
    rw [Matrix.trace_toLin'_eq]
    exact hT
  have := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hid htr
  simpa using this

/-- Theorem 17: if `Tr(Z^k) = 0` for every `k ≥ 1` in characteristic zero, `Z` is nilpotent. -/
theorem isNilpotent_of_trace_pow [CharZero K] (Z : Matrix n n K)
    (h : ∀ k, 0 < k → (Z ^ k).trace = 0) : IsNilpotent Z := by
  have hp : Z.charpoly ≠ 0 := (Matrix.charpoly_monic Z).ne_zero
  obtain ⟨q, hq, hnd⟩ := Z.charpoly.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  set m := Z.charpoly.rootMultiplicity 0 with hm
  simp only [map_zero, sub_zero] at hq hnd
  have hc : q.coeff 0 ≠ 0 := fun h0 => hnd (X_dvd_iff.2 h0)
  -- `X` and `q` are coprime, explicitly
  have hcop : IsCoprime (X : K[X]) q := by
    refine ⟨-(C (q.coeff 0)⁻¹ * divX q), C (q.coeff 0)⁻¹, ?_⟩
    have hsplit := divX_mul_X_add q
    have hunit : C (q.coeff 0)⁻¹ * C (q.coeff 0) = (1 : K[X]) := by
      rw [← C_mul, inv_mul_cancel₀ hc, C_1]
    calc -(C (q.coeff 0)⁻¹ * divX q) * X + C (q.coeff 0)⁻¹ * q
        = -(C (q.coeff 0)⁻¹ * divX q) * X
            + C (q.coeff 0)⁻¹ * (divX q * X + C (q.coeff 0)) := by rw [hsplit]
      _ = C (q.coeff 0)⁻¹ * C (q.coeff 0) := by ring
      _ = 1 := hunit
  obtain ⟨a, b, hab⟩ := (hcop.pow_left : IsCoprime ((X : K[X]) ^ (m + 1)) q)
  -- The projector `E = a(Z) Z^(m+1)`, and `F = b(Z) q(Z) = 1 - E`.
  obtain ⟨E, hE⟩ : ∃ E, E = aeval Z (a * X ^ (m + 1)) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = aeval Z (b * q) := ⟨_, rfl⟩
  have h1 : E + G = 1 := by
    rw [hE, hG, ← map_add, hab, map_one]
  have hCH : aeval Z (X ^ m * q) = 0 := by
    rw [← hq]
    exact Matrix.aeval_self_charpoly Z
  have hprod : E * G = 0 := by
    have e : a * X ^ (m + 1) * (b * q) = (a * b * X) * (X ^ m * q) := by ring
    rw [hE, hG, ← map_mul, e, map_mul, hCH, mul_zero]
  have hEE : E * E = E := by
    have h2 : G = 1 - E := eq_sub_of_add_eq' h1
    rw [h2, mul_sub, mul_one, sub_eq_zero] at hprod
    exact hprod.symm
  have hEtr : E.trace = 0 := by
    have e : a * X ^ (m + 1) = (a * X ^ m) * X := by ring
    rw [hE, e]
    exact trace_aeval_mul_X Z h _
  have hE0 : E = 0 := eq_zero_of_idempotent_of_trace E hEE hEtr
  -- Now `b(Z) q(Z) = 1`, and `Z^m q(Z) = 0` gives `Z^m = 0`.
  have hG1 : G = 1 := by rw [hE0, zero_add] at h1; exact h1
  have hZm : aeval Z ((X : K[X]) ^ m) = Z ^ m := by rw [map_pow, aeval_X]
  have e2 : (X : K[X]) ^ m * (b * q) = b * (X ^ m * q) := by ring
  have h3 : aeval Z ((X : K[X]) ^ m) * G = 0 := by
    rw [hG, ← map_mul, e2, map_mul, hCH, mul_zero]
  rw [hG1, mul_one, hZm] at h3
  exact ⟨m, h3⟩

variable {ι : Type*}

/-- The display of the proof of theorem 18. -/
theorem pow_eq_sum_commutators (Z : Matrix n n K) (s : Finset ι) (A B : ι → Matrix n n K)
    (hdef : Z = ∑ j ∈ s, (A j * B j - B j * A j)) (hZ : ∀ i ∈ s, Commute Z (A i)) (k : ℕ) :
    Z ^ (k + 1) = ∑ i ∈ s, (A i * (Z ^ k * B i) - (Z ^ k * B i) * A i) := by
  have e : Z ^ (k + 1) = Z ^ k * ∑ j ∈ s, (A j * B j - B j * A j) := by rw [pow_succ, ← hdef]
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hc : Z ^ k * A i = A i * Z ^ k := ((hZ i hi).pow_left k).eq
  rw [mul_sub, ← mul_assoc, hc, mul_assoc, mul_assoc]

/-- Theorem 18: `Z = ∑ [A_i, B_i]` commuting with all `A_j` is nilpotent, in characteristic 0. -/
theorem isNilpotent_sum_commutators [CharZero K] (Z : Matrix n n K) (s : Finset ι)
    (A B : ι → Matrix n n K) (hdef : Z = ∑ j ∈ s, (A j * B j - B j * A j))
    (hZ : ∀ i ∈ s, Commute Z (A i)) : IsNilpotent Z := by
  refine isNilpotent_of_trace_pow _ fun k hk => ?_
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  rw [pow_eq_sum_commutators Z s A B hdef hZ l, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

omit [DecidableEq n] in
/-- The invariance of the form of a representation, p. 34. -/
theorem trace_form_invariant (Sx Sy Sz : Matrix n n K) :
    ((Sx * Sy - Sy * Sx) * Sz).trace = (Sx * (Sy * Sz - Sz * Sy)).trace := by
  rw [sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_sub, mul_assoc Sx Sy Sz]
  congr 1
  rw [Matrix.trace_mul_comm (Sy * Sx) Sz, Matrix.trace_mul_comm Sx (Sz * Sy), mul_assoc]

end KaplanskyLie.TracePowers

#print axioms KaplanskyLie.TracePowers.trace_aeval_mul_X
#print axioms KaplanskyLie.TracePowers.eq_zero_of_idempotent_of_trace
#print axioms KaplanskyLie.TracePowers.isNilpotent_of_trace_pow
#print axioms KaplanskyLie.TracePowers.pow_eq_sum_commutators
#print axioms KaplanskyLie.TracePowers.isNilpotent_sum_commutators
#print axioms KaplanskyLie.TracePowers.trace_form_invariant
