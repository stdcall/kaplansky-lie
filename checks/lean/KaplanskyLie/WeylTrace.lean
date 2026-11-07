import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The equation `[A, B] = I` in characteristic `p`: theorems 76 and 77

Chapter I, § 7, pp. 71–72, theorem 76 (`th:commutator-identity-irreducible`) and the
theorem 77 that rests on it (`th:commutator-identity-trace`).

Notation.  `F` is a field, `R` a commutative ring in which `p = 0`; the book's operators
act on the right, so for linear maps its `x A B` is `B (A x)` and its `[A B] = I` is
`B (A v) = A (B v) + v`.  Matrices are written as in the book; the product `A₁ * B₁` of
matrices is the book's `A₁ B₁`.

* `card_eq_zero_of_commutator`, `dvd_of_commutator`: `Tr (A B - B A) = 0` forces
  `n = 0` in `F`, so `p ∣ n` (the divisibility behind theorem 76).
* `A₁`, `B₁`: the matrices of theorem 76, for every `p`.
* `A₁_mul_B₁_apply`, `B₁_mul_A₁_apply`: the products; `A₁ B₁` is the printed
  diagonal `1, 2, …, p - 1, 0`.
* `commutator_A₁_B₁`: `[A₁, B₁] = I` for every `p` when `p = 0` in `F`.
* `trace_A₁_mul_B₁_eq`: `Tr (A₁ B₁) = 1 + 2 + … + (p - 1)`.
* `trace_A₁_mul_B₁`: `Tr (A₁ B₁) = 0` for odd `p`; `trace_A₁_mul_B₁_two`: it is `1`
  for `p = 2`, so `p > 2` is needed.
* `trace_shifted`: `Tr ((λ + A₁)(μ + B₁)) = 0` for odd `p`, the printed expansion.
* `commute_iterate`, `commute_power_p`: `A^p` commutes with `B`: the first step of the
  proof.
* `relation_on_kernel`: `x A^(i+1) B = (i + 1) x A^i` for `x B = 0`.
* `linearIndependent_powers`: `x, x A, …, x A^(p-1)` are linearly independent for
  `x ≠ 0`, `x B = 0`: the second step.

Not covered: Schur's lemma and the normalisation (they need an algebraically closed
field: over a perfect field the printed statement fails, `checks/sage/chapter-1d.py`,
with `F_(q^d)^p` regarded as a space over `F_q`), the equality of `V` with the span of the
powers, the composition series of theorem 77.
-/

namespace KaplanskyLie.WeylTrace

open Finset Matrix

/-- `Tr (A B - B A) = 0` forces `n = 0` in the ring. -/
theorem card_eq_zero_of_commutator {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (h : A * B - B * A = 1) : (n : R) = 0 := by
  have h1 := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, Matrix.trace_one] at h1
  simpa using h1.symm

/-- Over a ring of characteristic `p`, `[A, B] = I` is possible only if `p ∣ n`. -/
theorem dvd_of_commutator {R : Type*} [CommRing R] {p n : ℕ} [CharP R p]
    (A B : Matrix (Fin n) (Fin n) R) (h : A * B - B * A = 1) : p ∣ n :=
  (CharP.cast_eq_zero_iff R p n).mp (card_eq_zero_of_commutator A B h)

section matrices

variable (p : ℕ) (R : Type*) [CommRing R]

/-- The matrix `A₁` of theorem 76: ones on the superdiagonal. -/
def A₁ : Matrix (Fin p) (Fin p) R := fun i j => if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

/-- The matrix `B₁` of theorem 76: `1, 2, …, p - 1` on the subdiagonal. -/
def B₁ : Matrix (Fin p) (Fin p) R := fun i j => if (i : ℕ) = (j : ℕ) + 1 then ((i : ℕ) : R) else 0

variable {p R}

theorem A₁_mul_B₁_apply (i j : Fin p) :
    (A₁ p R * B₁ p R) i j = if i = j ∧ (i : ℕ) + 1 < p then ((i : ℕ) + 1 : R) else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : (i : ℕ) + 1 < p
  · rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, h⟩ : Fin p)]
    · simp only [A₁, B₁]
      by_cases hij : i = j
      · subst hij
        simp [h]
      · have hne : ¬ ((i : ℕ) = (j : ℕ)) := fun e => hij (Fin.ext e)
        simp [hij, hne]
    · intro k _ hk
      have hne : ¬ ((k : ℕ) = (i : ℕ) + 1) := fun e => hk (Fin.ext e)
      simp [A₁, hne]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · have hz : ∀ k : Fin p, A₁ p R i k * B₁ p R k j = 0 := by
      intro k
      have hne : ¬ ((k : ℕ) = (i : ℕ) + 1) := by have := k.isLt; omega
      simp [A₁, hne]
    simp [hz, h]

theorem B₁_mul_A₁_apply (i j : Fin p) :
    (B₁ p R * A₁ p R) i j = if i = j then ((i : ℕ) : R) else 0 := by
  rw [Matrix.mul_apply]
  by_cases h0 : (i : ℕ) = 0
  · have hz : ∀ k : Fin p, B₁ p R i k * A₁ p R k j = 0 := by
      intro k
      have hne : ¬ ((i : ℕ) = (k : ℕ) + 1) := by omega
      simp [B₁, hne]
    simp only [hz, Finset.sum_const_zero]
    split_ifs <;> simp [h0]
  · have hlt : (i : ℕ) - 1 < p := by have := i.isLt; omega
    rw [Finset.sum_eq_single (⟨(i : ℕ) - 1, hlt⟩ : Fin p)]
    · have e1 : (i : ℕ) = (i : ℕ) - 1 + 1 := by omega
      simp only [B₁, A₁]
      by_cases hij : i = j
      · subst hij
        simp only [← e1, ite_true, mul_one]
      · have hne : ¬ ((j : ℕ) = (i : ℕ) - 1 + 1) := fun e => hij (Fin.ext (by omega))
        simp only [hij, hne, ite_false, mul_zero]
    · intro k _ hk
      have hne : ¬ ((i : ℕ) = (k : ℕ) + 1) := fun e => hk (Fin.ext (by simp; omega))
      simp [B₁, hne]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

/-- `[A₁, B₁] = I` whenever `p = 0` in the ring. -/
theorem commutator_A₁_B₁ (hp : (p : R) = 0) : A₁ p R * B₁ p R - B₁ p R * A₁ p R = 1 := by
  ext i j
  rw [Matrix.sub_apply, A₁_mul_B₁_apply, B₁_mul_A₁_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h : (i : ℕ) + 1 < p
    · simp [h]
    · have e : (i : ℕ) + 1 = p := by have := i.isLt; omega
      have e2 : ((i : ℕ) : R) + 1 = 0 := by
        have h1 := congrArg (Nat.cast : ℕ → R) e
        rw [Nat.cast_add, Nat.cast_one, hp] at h1
        exact h1
      simp only [h, and_false, ite_false, ite_true]
      linear_combination -e2
  · simp [hij]

theorem trace_A₁_mul_B₁_eq : Matrix.trace (A₁ p R * B₁ p R) = ((∑ i ∈ range p, i : ℕ) : R) := by
  simp only [Matrix.trace, Matrix.diag_apply, A₁_mul_B₁_apply, true_and]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < p then ((i : R) + 1) else 0) p]
  cases p with
  | zero => simp
  | succ q =>
    have hlast : ¬ (q + 1 < q + 1) := by omega
    rw [Finset.sum_range_succ, ite_eq_right_iff.mpr (fun h => absurd h hlast), add_zero,
      Finset.sum_range_succ' (fun i => i) q]
    push_cast
    rw [add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i + 1 < q + 1 := by have := mem_range.mp hi; omega
    simp only [hi', ite_true]

/-- `Tr (A₁ B₁) = 0` for odd `p`. -/
theorem trace_A₁_mul_B₁ (hodd : Odd p) (hp : (p : R) = 0) :
    Matrix.trace (A₁ p R * B₁ p R) = 0 := by
  rw [trace_A₁_mul_B₁_eq]
  obtain ⟨m, rfl⟩ := hodd
  have h := Finset.sum_range_id_mul_two (2 * m + 1)
  have h2 : (∑ i ∈ range (2 * m + 1), i) = (2 * m + 1) * m := by
    have e : (2 * m + 1) * (2 * m + 1 - 1) = (2 * m + 1) * m * 2 := by
      rw [Nat.add_sub_cancel]; ring
    rw [e] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  rw [h2, Nat.cast_mul, hp, zero_mul]

/-- For `p = 2` the trace is `1`: the hypothesis `p > 2` of theorems 76, 77 is needed. -/
theorem trace_A₁_mul_B₁_two : Matrix.trace (A₁ 2 (ZMod 2) * B₁ 2 (ZMod 2)) = 1 := by
  rw [trace_A₁_mul_B₁_eq]
  decide

theorem trace_A₁ : Matrix.trace (A₁ p R) = 0 := by
  simp [Matrix.trace, A₁]

theorem trace_B₁ : Matrix.trace (B₁ p R) = 0 := by
  simp [Matrix.trace, B₁]

/-- The expansion of the end of the proof of theorem 76. -/
theorem trace_shifted (lam mu : R) (hodd : Odd p) (hp : (p : R) = 0) :
    Matrix.trace ((lam • (1 : Matrix (Fin p) (Fin p) R) + A₁ p R) *
      (mu • (1 : Matrix (Fin p) (Fin p) R) + B₁ p R)) = 0 := by
  have e : (lam • (1 : Matrix (Fin p) (Fin p) R) + A₁ p R) *
      (mu • (1 : Matrix (Fin p) (Fin p) R) + B₁ p R) =
      (lam * mu) • (1 : Matrix (Fin p) (Fin p) R) + lam • B₁ p R + mu • A₁ p R +
        A₁ p R * B₁ p R := by
    rw [add_mul, mul_add, mul_add]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    rw [mul_comm mu lam]
    abel
  rw [e]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, trace_A₁, trace_B₁,
    trace_A₁_mul_B₁ hodd hp, Fintype.card_fin, hp]
  simp

end matrices

section abstract

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {A B : V →ₗ[F] V}

/-- `B (A^(i+1) v) = A^(i+1) (B v) + (i + 1) A^i v`. -/
theorem commute_iterate (hAB : ∀ v, B (A v) = A (B v) + v) (i : ℕ) (v : V) :
    B (A^[i + 1] v) = A^[i + 1] (B v) + ((i + 1 : ℕ) : F) • A^[i] v := by
  induction i with
  | zero => simp [hAB]
  | succ i ih =>
    rw [Function.iterate_succ_apply' A (i + 1), hAB, ih, map_add, map_smul,
      ← Function.iterate_succ_apply' A (i + 1), ← Function.iterate_succ_apply' A i,
      add_assoc, Nat.cast_succ (i + 1), add_smul, one_smul]

/-- The first step of the proof: `[B A^p] = 0`. -/
theorem commute_power_p {p : ℕ} [CharP F p] (hp0 : 0 < p) (hAB : ∀ v, B (A v) = A (B v) + v)
    (v : V) : B (A^[p] v) = A^[p] (B v) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [commute_iterate hAB, CharP.cast_eq_zero F (q + 1), zero_smul, add_zero]

/-- `x A^(i+1) B = (i + 1) x A^i` for `x B = 0`. -/
theorem relation_on_kernel (hAB : ∀ v, B (A v) = A (B v) + v) {x : V} (hx : B x = 0) (i : ℕ) :
    B (A^[i + 1] x) = ((i + 1 : ℕ) : F) • A^[i] x := by
  have h0 : A^[i + 1] (0 : V) = 0 := by
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, map_zero]
  rw [commute_iterate hAB, hx, h0, zero_add]

/-- The second step of the proof: `x, x A, …, x A^(p-1)` are linearly independent. -/
theorem linearIndependent_powers {p : ℕ} [hp : CharP F p]
    (hAB : ∀ v, B (A v) = A (B v) + v) {x : V} (hx : B x = 0) (hx0 : x ≠ 0) :
    LinearIndependent F (fun i : Fin p => A^[(i : ℕ)] x) := by
  have key : ∀ m : ℕ, m ≤ p → ∀ c : Fin m → F, ∑ i : Fin m, c i • A^[(i : ℕ)] x = 0 →
      ∀ i, c i = 0 := by
    intro m
    induction m with
    | zero => intro _ c _ i; exact i.elim0
    | succ m ih =>
      intro hm c hc
      have hsplit := hc
      rw [Fin.sum_univ_succ] at hsplit
      simp only [Fin.val_zero, Function.iterate_zero, id_eq, Fin.val_succ] at hsplit
      -- apply B
      have happ : ∑ i : Fin m, (c i.succ * ((i + 1 : ℕ) : F)) • A^[(i : ℕ)] x = 0 := by
        have h1 := congrArg B hsplit
        rw [map_add, map_smul, hx, smul_zero, zero_add, map_zero, map_sum] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, relation_on_kernel hAB hx, smul_smul]
      have hnext := ih (by omega) (fun i => c i.succ * ((i + 1 : ℕ) : F)) happ
      have hsucc : ∀ i : Fin m, c i.succ = 0 := by
        intro i
        have hne : ((i + 1 : ℕ) : F) ≠ 0 := by
          intro h0
          have hd := (CharP.cast_eq_zero_iff F p _).mp h0
          have := Nat.le_of_dvd (Nat.succ_pos _) hd
          have := i.isLt
          omega
        exact (mul_eq_zero.mp (hnext i)).resolve_right hne
      have h0 : c 0 • x = 0 := by
        have h2 : ∑ i : Fin m, c i.succ • A^[(i : ℕ) + 1] x = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hsucc i, zero_smul]
        rw [h2, add_zero] at hsplit
        exact hsplit
      have hc0 : c 0 = 0 := by
        by_contra hne
        apply hx0
        have h3 := inv_smul_smul₀ hne x
        rw [h0, smul_zero] at h3
        exact h3.symm
      intro i
      refine Fin.cases hc0 hsucc i
  rw [Fintype.linearIndependent_iff]
  exact fun c hc => key p le_rfl c hc

end abstract

end KaplanskyLie.WeylTrace

#print axioms KaplanskyLie.WeylTrace.card_eq_zero_of_commutator
#print axioms KaplanskyLie.WeylTrace.dvd_of_commutator
#print axioms KaplanskyLie.WeylTrace.A₁_mul_B₁_apply
#print axioms KaplanskyLie.WeylTrace.B₁_mul_A₁_apply
#print axioms KaplanskyLie.WeylTrace.commutator_A₁_B₁
#print axioms KaplanskyLie.WeylTrace.trace_A₁_mul_B₁_eq
#print axioms KaplanskyLie.WeylTrace.trace_A₁_mul_B₁
#print axioms KaplanskyLie.WeylTrace.trace_A₁_mul_B₁_two
#print axioms KaplanskyLie.WeylTrace.trace_A₁
#print axioms KaplanskyLie.WeylTrace.trace_B₁
#print axioms KaplanskyLie.WeylTrace.trace_shifted
#print axioms KaplanskyLie.WeylTrace.commute_iterate
#print axioms KaplanskyLie.WeylTrace.commute_power_p
#print axioms KaplanskyLie.WeylTrace.relation_on_kernel
#print axioms KaplanskyLie.WeylTrace.linearIndependent_powers
