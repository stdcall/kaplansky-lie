import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The steps with integer parts in Chapter II

`⌊x⌋₊` is the book's `[x]` (defined for `x ≥ 0`, p. 94).

* `add_floor_le`, `floor_add_le`: `[x] + [y] ≤ [x + y] ≤ [x] + [y] + 1` (the first paragraph of the
  proof of theorem 5, p. 95).
* `pow_floor_add`: `a^[x + y] = a^[x] a^[y] a^ε` with `ε = 0` or `1`: the corrected sentence of the proof
  of lemma 35, p. 126: the factor is `1` or `a_j`, and never `a_j²`.
* `tendsto_pow_floor_add`: the remark itself, as a statement on limits, for any topological group.
* `pow_floor_mul_le`: `p [r m] ≤ m` for `p r ≤ 1` (the proof of theorem 4, p. 94).
* `floor_le_floor_chain`: the chain in the proof of theorem 8, pp. 98.
* `abs_floor_sub_le`: `[r m]` and `[(r/k) [k m]]` differ by at most `r/k + 1`: the remark behind
  «непосредственно вытекает из теоремы 5» in theorem 9, p. 98.
* `two_mul_lt_of_strict`: the chain of the proof of lemma 19, pp. 115-116, with the corrected strict
  signs: `h < A n`, `h = [k m]`, `s ≤ [k m/(2 A)]` imply `2 s < n`.
* `mul_pow_mem_of_lt`: `a, b ∈ Q`, `2 s < n`, and `Q ^ j ⊆ U` for `j < n`, imply `(a b)^s ∈ U`: the
  corrected step on p. 115, with `a b ∈ Q²`.
* `le_of_one_lt_div`: `p/n_p > 1` gives `n_p ≤ p`: the corrected sentence on p. 112.

Not covered: the theorems that use these steps.
-/

namespace KaplanskyLie.FloorSteps

open Topology Filter Set
open scoped Pointwise

theorem add_floor_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : ⌊x⌋₊ + ⌊y⌋₊ ≤ ⌊x + y⌋₊ := by
  apply Nat.le_floor
  push_cast
  exact add_le_add (Nat.floor_le hx) (Nat.floor_le hy)

theorem floor_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : ⌊x + y⌋₊ ≤ ⌊x⌋₊ + ⌊y⌋₊ + 1 := by
  have h1 := Nat.lt_floor_add_one x
  have h2 := Nat.lt_floor_add_one y
  have : ⌊x + y⌋₊ < ⌊x⌋₊ + ⌊y⌋₊ + 2 := by
    rw [Nat.floor_lt (by positivity)]
    push_cast
    linarith
  omega

/-- The corrected reading of p. 126. -/
theorem pow_floor_add {G : Type*} [Group G] (a : G) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ ε : ℕ, ε ≤ 1 ∧ a ^ ⌊x + y⌋₊ = a ^ ⌊x⌋₊ * a ^ ⌊y⌋₊ * a ^ ε := by
  have h1 := add_floor_le hx hy
  have h2 := floor_add_le hx hy
  refine ⟨⌊x + y⌋₊ - (⌊x⌋₊ + ⌊y⌋₊), by omega, ?_⟩
  rw [← pow_add, ← pow_add]
  congr 1
  omega

/-- The remark of the first paragraph of the proof of theorem 5. -/
theorem tendsto_pow_floor_add {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {a : ℕ → G} {m : ℕ → ℕ} {r s : ℝ} {b c : G} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ha : Tendsto a atTop (𝓝 1))
    (hb : Tendsto (fun i => a i ^ ⌊r * m i⌋₊) atTop (𝓝 b))
    (hc : Tendsto (fun i => a i ^ ⌊s * m i⌋₊) atTop (𝓝 c)) :
    Tendsto (fun i => a i ^ ⌊(r + s) * m i⌋₊) atTop (𝓝 (b * c)) := by
  have hex : ∀ i, ∃ ε : ℕ, ε ≤ 1 ∧ a i ^ ⌊(r + s) * m i⌋₊ =
      a i ^ ⌊r * m i⌋₊ * a i ^ ⌊s * m i⌋₊ * a i ^ ε := by
    intro i
    have hr' : 0 ≤ r * m i := by positivity
    have hs' : 0 ≤ s * m i := by positivity
    have := pow_floor_add (a i) hr' hs'
    rwa [← add_mul] at this
  choose ε hε heq using hex
  have hsmall : Tendsto (fun i => a i ^ ε i) atTop (𝓝 1) := by
    rw [tendsto_def]
    intro V hV
    refine mem_of_superset (ha hV) fun i hi => ?_
    have hi' : a i ∈ V := hi
    have h1 : (1 : G) ∈ V := mem_of_mem_nhds hV
    have : ε i = 0 ∨ ε i = 1 := by have := hε i; omega
    rcases this with e | e
    · simpa [e] using h1
    · simpa [e] using hi'
  have := (hb.mul hc).mul hsmall
  simp only [mul_one] at this
  exact this.congr fun i => (heq i).symm

/-- The proof of theorem 4. -/
theorem pow_floor_mul_le {p m : ℕ} {r : ℝ} (hr : 0 ≤ r) (hp : (p : ℝ) * r ≤ 1) :
    p * ⌊r * m⌋₊ ≤ m := by
  have h1 : (⌊r * m⌋₊ : ℝ) ≤ r * m := Nat.floor_le (by positivity)
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have h2 : (p : ℝ) * ⌊r * m⌋₊ ≤ m := by
    calc (p : ℝ) * ⌊r * m⌋₊ ≤ p * (r * m) := mul_le_mul_of_nonneg_left h1 hp0
      _ = (p * r) * m := by ring
      _ ≤ 1 * m := mul_le_mul_of_nonneg_right hp hm0
      _ = m := one_mul _
  exact_mod_cast h2

/-- The chain of the proof of theorem 8. -/
theorem floor_le_floor_chain {k s r : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hkm : 2 ≤ k * m) (hr : r < k * s / 2) : ⌊r * m⌋₊ ≤ ⌊s * ⌊k * m⌋₊⌋₊ := by
  apply Nat.floor_le_floor
  have h1 := Nat.lt_floor_add_one (k * m)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have h2 : k * m / 2 ≤ ⌊k * m⌋₊ := by linarith
  calc r * m ≤ (k * s / 2) * m := mul_le_mul_of_nonneg_right hr.le hm0
    _ = s * (k * m / 2) := by ring
    _ ≤ s * ⌊k * m⌋₊ := mul_le_mul_of_nonneg_left h2 hs

/-- Theorem 9: the exponents `[r m]` and `[(r/k) [k m]]` differ boundedly. -/
theorem abs_floor_sub_le {r k : ℝ} {m : ℕ} (hr : 0 ≤ r) (hk : 0 < k) :
    |(⌊r * m⌋₊ : ℝ) - ⌊r / k * ⌊k * m⌋₊⌋₊| ≤ r / k + 1 := by
  have hk' : 0 ≤ r / k := by positivity
  have hkm : 0 ≤ k * m := by positivity
  have h1 := Nat.floor_le hkm
  have h2 := Nat.lt_floor_add_one (k * m)
  have hrm : 0 ≤ r * m := by positivity
  have hb : 0 ≤ r / k * ⌊k * m⌋₊ := by positivity
  have a1 := Nat.floor_le hrm
  have a2 := Nat.lt_floor_add_one (r * m)
  have b1 := Nat.floor_le hb
  have b2 := Nat.lt_floor_add_one (r / k * ⌊k * m⌋₊)
  have e : r * m = r / k * (k * m) := by field_simp
  have c1 : r / k * ⌊k * m⌋₊ ≤ r / k * (k * m) := mul_le_mul_of_nonneg_left h1 hk'
  have c2 : r / k * (k * m) ≤ r / k * (⌊k * m⌋₊ + 1) := mul_le_mul_of_nonneg_left h2.le hk'
  rw [abs_le]
  constructor <;> nlinarith

/-- The chain of the proof of lemma 19, with the corrected strict signs. -/
theorem two_mul_lt_of_strict {k : ℝ} {m A n s : ℕ} (hk : 0 ≤ k) (hA : 0 < A)
    (hh : ⌊k * m⌋₊ < A * n) (hs : s ≤ ⌊k * m / (2 * A)⌋₊) : 2 * s < n := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have h0 : 0 ≤ k * m / (2 * A) := by positivity
  have h1 : (s : ℝ) ≤ k * m / (2 * A) := by
    calc (s : ℝ) ≤ ⌊k * m / (2 * A)⌋₊ := by exact_mod_cast hs
      _ ≤ _ := Nat.floor_le h0
  have h2 : (2 * A * s : ℝ) ≤ k * m := by
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have h3 : 2 * A * s ≤ ⌊k * m⌋₊ := Nat.le_floor (by exact_mod_cast h2)
  have h4 : A * (2 * s) < A * n := by
    calc A * (2 * s) = 2 * A * s := by ring
      _ ≤ _ := h3
      _ < _ := hh
  exact Nat.lt_of_mul_lt_mul_left h4

/-- The corrected step on p. 115: `a b ∈ Q²` and `(a b)^s ∈ Q^(2 s) ⊆ U` for `2 s < n`. -/
theorem mul_pow_mem_of_lt {G : Type*} [Group G] {Q U : Set G} {n s : ℕ} {a b : G} (ha : a ∈ Q)
    (hb : b ∈ Q) (hU : ∀ j < n, Q ^ j ⊆ U) (hs : 2 * s < n) : (a * b) ^ s ∈ U := by
  refine hU _ hs ?_
  rw [pow_mul, pow_two]
  exact pow_mem_pow (mul_mem_mul ha hb)

/-- The corrected sentence on p. 112. -/
theorem le_of_one_lt_div {p n : ℕ} (hn : 0 < n) (h : (1 : ℝ) < (p : ℝ) / n) : n ≤ p := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lt_div_iff₀ hn'] at h
  have : (n : ℝ) ≤ p := by linarith
  exact_mod_cast this

end KaplanskyLie.FloorSteps

#print axioms KaplanskyLie.FloorSteps.add_floor_le
#print axioms KaplanskyLie.FloorSteps.floor_add_le
#print axioms KaplanskyLie.FloorSteps.pow_floor_add
#print axioms KaplanskyLie.FloorSteps.tendsto_pow_floor_add
#print axioms KaplanskyLie.FloorSteps.pow_floor_mul_le
#print axioms KaplanskyLie.FloorSteps.floor_le_floor_chain
#print axioms KaplanskyLie.FloorSteps.abs_floor_sub_le
#print axioms KaplanskyLie.FloorSteps.two_mul_lt_of_strict
#print axioms KaplanskyLie.FloorSteps.mul_pow_mem_of_lt
#print axioms KaplanskyLie.FloorSteps.le_of_one_lt_div
