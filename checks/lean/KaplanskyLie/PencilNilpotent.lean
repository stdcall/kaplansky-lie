import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-!
# A pencil of nilpotent matrices

Chapter I, § 4, theorem 44, p. 47: if `A`, `B` are `n × n` matrices over a field and `k A + B` is
nilpotent for `n + 1` different scalars `k`, then `B` is nilpotent.  The book expands
`(k A + B)^n = 0` in powers of `k` and inverts a Vandermonde matrix: all `n + 1` "unknowns", the
matrix coefficients of the powers of `k`, vanish.  Here the same statement is that the matrix
`(X A + B)^n` over `K[X]` is zero; the proof counts roots of its entries, polynomials of degree
at most `n`, instead of naming the Vandermonde determinant.

* `pow_card_eq_zero_of_isNilpotent`: a nilpotent `n × n` matrix over a field has `M^n = 0`
  (the book uses this silently when writing `(k A + B)^n = 0`).
* `natDegree_pencil_pow_le`: the entries of `(X A + B)^m` have degree at most `m`.
* `pencil_pow_eq_zero`: `(X A + B)^n = 0`, all unknowns of the proof vanish.
* `pencil_nilpotent`: theorem 44, with `B^n = 0`.

Notation: `n` of the book is `Fintype.card n`; `S` is the set of the `n + 1` scalars.  The field is
arbitrary, as in the book.  Not covered: the application in theorem 45; that `n + 1` cannot be
lowered (the family of cyclic matrices in `checks/sage/chapter-1b.py`).
-/

namespace KaplanskyLie.PencilNilpotent

open Polynomial Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- A nilpotent `n × n` matrix over a field satisfies `M^n = 0`. -/
theorem pow_card_eq_zero_of_isNilpotent {M : Matrix n n K} (hM : IsNilpotent M) :
    M ^ Fintype.card n = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM
  have h0 : M.charpoly - X ^ Fintype.card n = 0 := h.eq_zero
  have h1 : M.charpoly = X ^ Fintype.card n := sub_eq_zero.1 h0
  have h2 := Matrix.aeval_self_charpoly M
  rw [h1] at h2
  simpa using h2

/-- The matrix `X A + B` over `K[X]`. -/
noncomputable def pencil (A B : Matrix n n K) : Matrix n n K[X] :=
  (X : K[X]) • A.map C + B.map C

omit [Fintype n] [DecidableEq n] in
theorem natDegree_pencil_le (A B : Matrix n n K) (i j : n) : (pencil A B i j).natDegree ≤ 1 := by
  simp only [pencil, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
  exact natDegree_mul_le.trans (by simp)

/-- The entries of `(X A + B)^m` have degree at most `m`. -/
theorem natDegree_pencil_pow_le (A B : Matrix n n K) (m : ℕ) (i j : n) :
    ((pencil A B ^ m) i j).natDegree ≤ m := by
  induction m generalizing i j with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      split_ifs <;> simp
  | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      refine natDegree_sum_le_of_forall_le _ _ fun l _ => ?_
      exact natDegree_mul_le.trans (add_le_add (ih i l) (natDegree_pencil_le A B l j))

/-- Specialising `X` to `k` in `(X A + B)^m`. -/
theorem eval_pencil_pow (A B : Matrix n n K) (k : K) (m : ℕ) (i j : n) :
    ((pencil A B ^ m) i j).eval k = ((k • A + B) ^ m) i j := by
  have hmap : (evalRingHom k).mapMatrix (pencil A B) = k • A + B := by
    ext a b
    simp [pencil]
    ring
  have := congrArg (fun M : Matrix n n K => M i j)
    (map_pow (evalRingHom k).mapMatrix (pencil A B) m)
  simp only [hmap] at this
  simpa using this

/-- All unknowns of the proof vanish: `(X A + B)^n = 0` over `K[X]`. -/
theorem pencil_pow_eq_zero (A B : Matrix n n K) (S : Finset K)
    (hS : S.card = Fintype.card n + 1) (h : ∀ k ∈ S, IsNilpotent (k • A + B)) :
    pencil A B ^ Fintype.card n = 0 := by
  refine Matrix.ext fun i j => ?_
  have hdeg := natDegree_pencil_pow_le A B (Fintype.card n) i j
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S (fun k hk => ?_) (by omega)
  rw [eval_pencil_pow, pow_card_eq_zero_of_isNilpotent (h k hk)]
  rfl

/-- Theorem 44: if `k A + B` is nilpotent for `n + 1` different `k`, then `B` is nilpotent; in
fact `B^n = 0`. -/
theorem pencil_nilpotent (A B : Matrix n n K) (S : Finset K) (hS : S.card = Fintype.card n + 1)
    (h : ∀ k ∈ S, IsNilpotent (k • A + B)) : B ^ Fintype.card n = 0 := by
  ext i j
  have h0 := pencil_pow_eq_zero A B S hS h
  have := eval_pencil_pow A B 0 (Fintype.card n) i j
  rw [h0] at this
  simpa using this.symm

end KaplanskyLie.PencilNilpotent

#print axioms KaplanskyLie.PencilNilpotent.pow_card_eq_zero_of_isNilpotent
#print axioms KaplanskyLie.PencilNilpotent.natDegree_pencil_pow_le
#print axioms KaplanskyLie.PencilNilpotent.pencil_pow_eq_zero
#print axioms KaplanskyLie.PencilNilpotent.pencil_nilpotent
