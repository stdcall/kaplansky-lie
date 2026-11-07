import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Representations of the three-dimensional algebra: theorem 58

Chapter I, § 5, pp. 55–57: theorem 58 (`th:sl2-triple-vector`), formulas (6)
(`eq:sl2-h-action`) and (7) (`eq:sl2-x-action`), and the last statement
`λ = -(r - 1)/2`; the statement for any characteristic is used in § 8.

Notation.  `K` is a commutative ring (a field for the last statement), `V` a
module, `A X H` linear maps of `V`.  The book writes operators on the right, so
its `u A^i H` is `H (A^[i] u)` here, and its `[A H] = A H - H A = A` is
`H (A v) - A (H v) = A v`.  The number `½ i (i - 1)` of (7) is the integer
`i.choose 2`, which makes (7) meaningful in every characteristic.  The third relation
of the theorem, `[X H] = -X`, is not needed for (6), (7) and is not assumed.

* `eq6`: formula (6) for every `i`.
* `eq7`: formula (7): `u A^(i+1) X = [(i + 1) λ + C(i + 1, 2)] u A^i`, every `i`
  (for `i = 0` of the book both sides of (7) are `0` since `u X = 0`).
* `string_relation`: if `u A^r = 0`, `r ≥ 1`, and `u A^(r-1) ≠ 0`, then
  `r λ + C(r, 2) = 0`.
* `last_statement`: if moreover `r ≠ 0` in `K` (`K` a field), then
  `2 λ = -(r - 1)`, that is `λ = -(r - 1)/2` in characteristic not `2`.
* `last_statement_odd`: for odd `r = 2 m + 1` with `r ≠ 0` in `K`, `λ = -m`; this is
  the reading of the remark for `p = 2`: `(r - 1)/2` is the integer `m`, not a
  function of the residue of `r`.

The hypothesis `u A^(r-1) ≠ 0` contains `u ≠ 0` for `r = 1`; for `u = 0` the printed
statement (with `r = 1`) would force `λ = 0` for every `λ`: "ненулевой вектор"
is needed (`checks/sage/chapter-1c.py`).

Not covered: the passage to `L` (`A = R_a`, `X = R_x`, `H = R_h`); it is checked
on all root systems up to rank 8 in `checks/sage/chapter-1c.py`.
-/

namespace KaplanskyLie.SlTwoString

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- The hypotheses of theorem 58, in the notation of function application. -/
structure Triple (A X H : V →ₗ[K] V) : Prop where
  /-- `[A H] = A` -/
  ah : ∀ v, H (A v) = A (H v) + A v
  /-- `[A X] = H` -/
  ax : ∀ v, X (A v) = A (X v) + H v

variable {A X H : V →ₗ[K] V} {u : V} {lam : K}

/-- Formula (6): `u A^i H = (λ + i) u A^i`. -/
theorem eq6 (T : Triple A X H) (hH : H u = lam • u) (i : ℕ) :
    H (A^[i] u) = (lam + i) • A^[i] u := by
  induction i with
  | zero => simpa using hH
  | succ i ih =>
    rw [Function.iterate_succ_apply', T.ah, ih, map_smul, Nat.cast_succ, ← add_assoc]
    simp only [add_smul, one_smul]

/-- Formula (7): `u A^(i+1) X = [(i + 1) λ + C(i + 1, 2)] u A^i`. -/
theorem eq7 (T : Triple A X H) (hX : X u = 0) (hH : H u = lam • u) (i : ℕ) :
    X (A^[i + 1] u) = (((i + 1 : ℕ) : K) * lam + ((i + 1).choose 2 : ℕ)) • A^[i] u := by
  induction i with
  | zero =>
    simp only [Function.iterate_one, zero_add, Function.iterate_zero, id_eq]
    rw [T.ax, hX, map_zero, zero_add, hH]
    simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', T.ax, ih, map_smul, eq6 T hH,
      ← Function.iterate_succ_apply' A, ← add_smul]
    congr 1
    have hc : ((i + 1 + 1).choose 2 : ℕ) = (i + 1).choose 2 + (i + 1) := by
      rw [Nat.choose_succ_succ' (i + 1) 1, Nat.choose_one_right, add_comm]
    rw [hc]
    push_cast
    ring

/-- The relation at the end of the proof: `r λ + C(r, 2) = 0`. -/
theorem string_relation {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {A X H : V →ₗ[K] V} {u : V} {lam : K} (T : Triple A X H) (hX : X u = 0)
    (hH : H u = lam • u) {r : ℕ} (hr0 : 0 < r) (hr : A^[r] u = 0) (hne : A^[r - 1] u ≠ 0) :
    (r : K) * lam + (r.choose 2 : ℕ) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have h := eq7 T hX hH s
  rw [hr, map_zero] at h
  simp only [Nat.add_sub_cancel] at hne
  by_contra hc
  apply hne
  have h1 := inv_smul_smul₀ hc (A^[s] u)
  rw [← h, smul_zero] at h1
  exact h1.symm

theorem two_mul_choose_two (r : ℕ) (K : Type*) [CommRing K] :
    2 * ((r.choose 2 : ℕ) : K) = (r : K) * ((r : K) - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.choose_succ_succ' r 1, Nat.choose_one_right]
    push_cast
    linear_combination ih

/-- The last statement of theorem 58 in the form `2 λ = -(r - 1)`. -/
theorem last_statement {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {A X H : V →ₗ[K] V} {u : V} {lam : K} (T : Triple A X H) (hX : X u = 0)
    (hH : H u = lam • u) {r : ℕ} (hr0 : 0 < r) (hr : A^[r] u = 0) (hne : A^[r - 1] u ≠ 0)
    (hp : (r : K) ≠ 0) : 2 * lam = -((r : K) - 1) := by
  have h := string_relation T hX hH hr0 hr hne
  have h2 := two_mul_choose_two r K
  have : (r : K) * (2 * lam + ((r : K) - 1)) = 0 := by
    linear_combination 2 * h - h2
  have h3 := (mul_eq_zero.mp this).resolve_left hp
  linear_combination h3

/-- For odd `r = 2 m + 1`, `λ = -m`, in every characteristic where `r ≠ 0`; for `p = 2`
this is the reading of the remark after the theorem. -/
theorem last_statement_odd {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {A X H : V →ₗ[K] V} {u : V} {lam : K} (T : Triple A X H) (hX : X u = 0)
    (hH : H u = lam • u) {m : ℕ} (hr : A^[2 * m + 1] u = 0) (hne : A^[2 * m] u ≠ 0)
    (hp : ((2 * m + 1 : ℕ) : K) ≠ 0) : lam = -(m : K) := by
  have h := string_relation T hX hH (Nat.succ_pos _) hr (by simpa using hne)
  have hc : (2 * m + 1).choose 2 = (2 * m + 1) * m := by
    have h2 : ∀ n : ℕ, (2 * n + 1).choose 2 = (2 * n + 1) * n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        have e1 : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
        rw [e1, Nat.choose_succ_succ' ((2 * n + 1) + 1) 1, Nat.choose_one_right,
          Nat.choose_succ_succ' (2 * n + 1) 1, Nat.choose_one_right, ih]
        ring
    exact h2 m
  rw [hc] at h
  have h4 : ((2 * m + 1 : ℕ) : K) * (lam + m) = 0 := by
    push_cast at h ⊢
    linear_combination h
  have h5 := (mul_eq_zero.mp h4).resolve_left hp
  linear_combination h5

end KaplanskyLie.SlTwoString

#print axioms KaplanskyLie.SlTwoString.eq6
#print axioms KaplanskyLie.SlTwoString.eq7
#print axioms KaplanskyLie.SlTwoString.string_relation
#print axioms KaplanskyLie.SlTwoString.two_mul_choose_two
#print axioms KaplanskyLie.SlTwoString.last_statement
#print axioms KaplanskyLie.SlTwoString.last_statement_odd
