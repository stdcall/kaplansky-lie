import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Abel

/-!
# Characteristic subspaces of derivations and automorphisms

Chapter I, § 2, theorems 14 and 15 with formula (4), pp. 26-27; § 4, theorem 43, p. 46.  Let `A` be
an algebra over a field `K`, not necessarily Lie or associative, as in the book: a
non-unital non-associative ring with a compatible `K`-module structure.  The book writes operators
on the right, `x D`; here `D x`, which changes nothing, because only one operator is
applied at a time.  `(D - α)` is `D - α • 1`, an element of `Module.End K A`.

* `derivation_shift`: formula (4), `(x y)(D - α - β) = x(D - α) · y + x · y(D - β)`.
* `derivation_power`: theorem 14 with the exponent of the proof: if `x(D - α)^r = 0`,
  `y(D - β)^s = 0`, then `(x y)(D - α - β)^N = 0` for `N ≥ r + s - 1`.
* `automorphism_shift`: the identity of the proof of theorem 15,
  `(x y)(T - α β) = x(T - α) · β y + x T · y(T - β)`.
* `automorphism_power`: theorem 15 with the same exponent.
* `root_space_product`: theorem 43 for one vector: if `x` lies in the root space of `α` and `y` in
  that of `β` for a family of derivations `D : ι → End A` (the book: a nilpotent Lie algebra `E`
  of derivations; only that each is a derivation is used), then `x y` lies in the root space of
  `α + β`.

Finite dimension and algebraic closure, the hypotheses of the book, serve only to decompose `A`
into these subspaces, which is not formalised.  Not covered: theorem 16, whose proof combines
theorem 15 with theorem 13; examples in `checks/sage/chapter-1a.py`.
-/

namespace KaplanskyLie.CharacteristicSubspaces

variable {K A : Type*} [Field K] [NonUnitalNonAssocRing A] [Module K A]
  [SMulCommClass K A A] [IsScalarTower K A A]

/-- `D` is a derivation of `A`. -/
def IsDer (D : Module.End K A) : Prop := ∀ x y : A, D (x * y) = D x * y + x * D y

/-- `T` is multiplicative. -/
def IsMult (T : Module.End K A) : Prop := ∀ x y : A, T (x * y) = T x * T y

/-- `D - α`. -/
def sh (D : Module.End K A) (α : K) : Module.End K A := D - α • 1

omit [SMulCommClass K A A] [IsScalarTower K A A] in
theorem sh_apply (D : Module.End K A) (α : K) (x : A) : sh D α x = D x - α • x := by
  simp [sh]

/-- Formula (4). -/
theorem derivation_shift {D : Module.End K A} (hD : IsDer D) (α β : K) (x y : A) :
    sh D (α + β) (x * y) = sh D α x * y + x * sh D β y := by
  rw [sh_apply, sh_apply, sh_apply, hD, sub_mul, mul_sub, add_smul, smul_mul_assoc,
    mul_smul_comm]
  abel

/-- Theorem 14: the exponent `r + s - 1` of the proof. -/
theorem derivation_power {D : Module.End K A} (hD : IsDer D) (α β : K) (N : ℕ) :
    ∀ (r s : ℕ) (x y : A), (sh D α ^ r) x = 0 → (sh D β ^ s) y = 0 → r + s ≤ N + 1 →
      (sh D (α + β) ^ N) (x * y) = 0 := by
  induction N with
  | zero =>
      intro r s x y hx hy hrs
      have : r = 0 ∨ s = 0 := by omega
      rcases this with rfl | rfl
      · have h0 : x = 0 := by simpa using hx
        simp [h0]
      · have h0 : y = 0 := by simpa using hy
        simp [h0]
  | succ N ih =>
      intro r s x y hx hy hrs
      rcases r with _ | r
      · have h0 : x = 0 := by simpa using hx
        simp [h0]
      rcases s with _ | s
      · have h0 : y = 0 := by simpa using hy
        simp [h0]
      rw [pow_succ, Module.End.mul_apply, derivation_shift hD, map_add]
      have hx' : (sh D α ^ r) (sh D α x) = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ]
        exact hx
      have hy' : (sh D β ^ s) (sh D β y) = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ]
        exact hy
      rw [ih r (s + 1) _ y hx' hy (by omega), ih (r + 1) s x _ hx hy' (by omega), add_zero]

/-- The identity of the proof of theorem 15. -/
theorem automorphism_shift {T : Module.End K A} (hT : IsMult T) (α β : K) (x y : A) :
    sh T (α * β) (x * y) = sh T α x * (β • y) + T x * sh T β y := by
  rw [sh_apply, sh_apply, sh_apply, hT, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    mul_smul_comm, smul_smul]
  abel

/-- Theorem 15: `(x y)(T - α β)^N = 0` for `N ≥ r + s - 1`. -/
theorem automorphism_power {T : Module.End K A} (hT : IsMult T) (α β : K) (N : ℕ) :
    ∀ (r s : ℕ) (x y : A), (sh T α ^ r) x = 0 → (sh T β ^ s) y = 0 → r + s ≤ N + 1 →
      (sh T (α * β) ^ N) (x * y) = 0 := by
  induction N with
  | zero =>
      intro r s x y hx hy hrs
      have : r = 0 ∨ s = 0 := by omega
      rcases this with rfl | rfl
      · have h0 : x = 0 := by simpa using hx
        simp [h0]
      · have h0 : y = 0 := by simpa using hy
        simp [h0]
  | succ N ih =>
      intro r s x y hx hy hrs
      rcases r with _ | r
      · have h0 : x = 0 := by simpa using hx
        simp [h0]
      rcases s with _ | s
      · have h0 : y = 0 := by simpa using hy
        simp [h0]
      rw [pow_succ, Module.End.mul_apply, automorphism_shift hT, map_add]
      have hx' : (sh T α ^ r) (sh T α x) = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ]
        exact hx
      have hy' : (sh T β ^ s) (sh T β y) = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ]
        exact hy
      have hβ : (sh T β ^ (s + 1)) (β • y) = 0 := by
        rw [map_smul, hy, smul_zero]
      -- `T` commutes with `T - α`
      have hc : Commute T (sh T α) := by
        show T * (T - α • 1) = (T - α • 1) * T
        rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      have hTx : (sh T α ^ (r + 1)) (T x) = 0 := by
        rw [← Module.End.mul_apply, ← (hc.pow_right (r + 1)).eq, Module.End.mul_apply, hx, map_zero]
      rw [ih r (s + 1) _ _ hx' hβ (by omega), ih (r + 1) s _ _ hTx hy' (by omega), add_zero]

/-- Theorem 43 for one pair of vectors: the product of root vectors for `α`, `β` is a root
vector for `α + β`, for a family of derivations. -/
theorem root_space_product {ι : Type*} (D : ι → Module.End K A) (hD : ∀ i, IsDer (D i))
    (α β : ι → K) (x y : A) (hx : ∀ i, ∃ r, (sh (D i) (α i) ^ r) x = 0)
    (hy : ∀ i, ∃ s, (sh (D i) (β i) ^ s) y = 0) :
    ∀ i, ∃ N, (sh (D i) (α i + β i) ^ N) (x * y) = 0 := by
  intro i
  obtain ⟨r, hr⟩ := hx i
  obtain ⟨s, hs⟩ := hy i
  exact ⟨r + s, derivation_power (hD i) _ _ (r + s) r s x y hr hs (by omega)⟩

end KaplanskyLie.CharacteristicSubspaces

#print axioms KaplanskyLie.CharacteristicSubspaces.derivation_shift
#print axioms KaplanskyLie.CharacteristicSubspaces.derivation_power
#print axioms KaplanskyLie.CharacteristicSubspaces.automorphism_shift
#print axioms KaplanskyLie.CharacteristicSubspaces.automorphism_power
#print axioms KaplanskyLie.CharacteristicSubspaces.root_space_product
