import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Characteristic subspaces under a transformation with a repeated commutator zero

Chapter I, § 4, theorem 40, p. 44.  Let `S`, `T` be linear transformations with
`[... [[S T] T] ...] = 0`, `n` copies of `T`.  If `x T^r = 0` then `x S T^(n+r-1) = 0`; applied to
`T - c`, this shows that the characteristic subspaces of `T` are invariant under `S`.

The transformations are elements of a ring `R`, acting on the right of `M` as in the book: `M` is
a module over the opposite ring and `x <• S` is the book's `x S`, so that
`x <• (S * T) = x <• S <• T`.  `ad T S = S T - T S` is the book's `[S T]`, and the hypothesis is
`(ad T)^[n] S = 0`.

* `repeated_commutator`: `x T^r = 0` and `(ad T)^[n] S = 0` imply `x S T^N = 0` whenever
  `n + r ≤ N + 1`; the exponent `N = n + r - 1` of the book is the smallest case.  The book
  derives this by an induction on `i` of the statement `x T^(r-i) S T^(n+i-1) = 0`, from the
  expansion of the repeated commutator; here the double induction on `n` and `r` uses only
  `S T = [S T] + T S`.
* `ad_sub_algebraMap`: `ad (T - c) = ad T`, "nothing changes if a scalar is subtracted from `T`".
* `characteristic_subspace_invariant`: the conclusion of the theorem with `T - c`.

Not covered: theorem 41, which applies this repeatedly to a nilpotent Lie algebra of matrices;
existence of the decomposition into characteristic subspaces.
-/

namespace KaplanskyLie.RepeatedCommutator

open scoped RightActions

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The book's `[S T]`, as a function of `S`. -/
def ad (T S : R) : R := S * T - T * S

theorem rsmul_rsmul (x : M) (a b : R) : x <• a <• b = x <• (a * b) := by
  show MulOpposite.op b • MulOpposite.op a • x = MulOpposite.op (a * b) • x
  rw [smul_smul, MulOpposite.op_mul]

/-- Theorem 40, in the form with any exponent `N ≥ n + r - 1`. -/
theorem repeated_commutator (T : R) :
    ∀ (n r : ℕ) (S : R) (x : M) (N : ℕ), (ad T)^[n] S = 0 → x <• T ^ r = 0 → n + r ≤ N + 1 →
      x <• S <• T ^ N = 0 := by
  intro n
  induction n with
  | zero =>
      intro r S x N hS _ _
      have h0 : S = 0 := hS
      rw [h0]
      simp
  | succ n ihn =>
      intro r
      induction r with
      | zero =>
          intro S x N _ hx _
          have h0 : x = 0 := by simpa using hx
          rw [h0]
          simp
      | succ r ihr =>
          intro S x N hS hx hN
          obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
          have hxT : (x <• T) <• T ^ r = 0 := by
            rw [rsmul_rsmul, ← pow_succ']
            exact hx
          have h1 : x <• ad T S <• T ^ N' = 0 :=
            ihn (r + 1) (ad T S) x N' hS hx (by omega)
          have h2 : (x <• T) <• S <• T ^ N' = 0 :=
            ihr S (x <• T) N' hS hxT (by omega)
          -- `S T^(N'+1) = [S T] T^N' + T S T^N'`
          have split : S * T = ad T S + T * S := by simp [ad]
          have e : S * T ^ (N' + 1) = ad T S * T ^ N' + T * (S * T ^ N') := by
            rw [pow_succ', ← mul_assoc, split, add_mul, mul_assoc]
          have key : x <• S <• T ^ (N' + 1)
              = x <• ad T S <• T ^ N' + (x <• T) <• S <• T ^ N' := by
            calc x <• S <• T ^ (N' + 1) = x <• (S * T ^ (N' + 1)) := rsmul_rsmul _ _ _
              _ = x <• (ad T S * T ^ N' + T * (S * T ^ N')) := by rw [e]
              _ = x <• (ad T S * T ^ N') + x <• (T * (S * T ^ N')) := by
                  rw [MulOpposite.op_add, add_smul]
              _ = x <• ad T S <• T ^ N' + (x <• T) <• S <• T ^ N' := by
                  rw [rsmul_rsmul x (ad T S), rsmul_rsmul (x <• T) S, rsmul_rsmul x T]
          rw [key, h1, h2, add_zero]

variable {K : Type*} [Field K] [Algebra K R]

/-- "Nothing changes if a scalar is subtracted from `T`." -/
theorem ad_sub_algebraMap (T : R) (c : K) : ad (T - algebraMap K R c) = ad T := by
  funext S
  have hc : algebraMap K R c * S = S * algebraMap K R c := Algebra.commutes c S
  simp only [ad, mul_sub, sub_mul, hc]
  abel

/-- Theorem 40 for `T - c`: if `x (T - c)^r = 0` and the `n`-fold commutator of `S` with `T`
vanishes, then `x S (T - c)^(n+r-1) = 0`.  So `S` preserves the characteristic subspaces of `T`. -/
theorem characteristic_subspace_invariant (S T : R) (c : K) (x : M) (n r : ℕ)
    (hS : (ad T)^[n] S = 0) (hx : x <• (T - algebraMap K R c) ^ r = 0) :
    x <• S <• (T - algebraMap K R c) ^ (n + r - 1) = 0 := by
  refine repeated_commutator (T - algebraMap K R c) n r S x _ ?_ hx (by omega)
  rw [ad_sub_algebraMap]
  exact hS

end KaplanskyLie.RepeatedCommutator

#print axioms KaplanskyLie.RepeatedCommutator.repeated_commutator
#print axioms KaplanskyLie.RepeatedCommutator.ad_sub_algebraMap
#print axioms KaplanskyLie.RepeatedCommutator.characteristic_subspace_invariant
