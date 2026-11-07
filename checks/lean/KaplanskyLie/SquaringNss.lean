import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Group

/-!
# Squaring is injective near `1` in an `NSS`-group (theorem 3 of Chapter II)

Chapter II, § 2, pp. 92-93 (theorem 3), and p. 119, § 8: «Из того, что квадратный корень в `U`
извлекается единственным образом, следует, что ограничение этого отображения на `K₁` является
взаимно однозначным»; the same uniqueness closes the proof of theorem 16, p. 132.

Notation.  `W` is the compact symmetric neighbourhood of `1` of the proof, containing no subgroup
except `{1}` (`NoSubgroupIn W`).  The book deduces from local compactness that such a `W` exists
and from theorem 2 that `G` is metrizable; here `W` and the first countability are hypotheses.

* `conj_eq_inv`: `y⁻¹ a y = a⁻¹` for `a = x y⁻¹`, `x² = y²` (the identity of p. 92, in every group).
* `conj_pow_eq_inv`: `y⁻¹ a^k y = a^(-k)`.
* `eq_one_of_forall_pow_mem`: an element with all powers in the symmetric `W` is `1`.
* `square_injective`: theorem 3.
* `onePar_eq`: two one-parameter subgroups `X`, `Y` with `X(t)`, `Y(t)` in a set `U` on which squaring
  is injective, for `|t| ≤ 1`, and with `X 1 = Y 1`, coincide.  The dyadic points are by the
  uniqueness of square roots, the others by continuity; `T2Space G` is needed.

Not covered: the existence of `W` (local compactness), theorem 2.
-/

namespace KaplanskyLie.SquaringNss

open Topology Filter Set

/-- `{1}` is the only subgroup contained in `U`. -/
def NoSubgroupIn {G : Type*} [Group G] (U : Set G) : Prop :=
  ∀ S : Subgroup G, (S : Set G) ⊆ U → S = ⊥

theorem eq_one_of_forall_zpow_mem {G : Type*} [Group G] {U : Set G}
    (hU : NoSubgroupIn U) {x : G} (hx : ∀ k : ℤ, x ^ k ∈ U) : x = 1 := by
  have hS : Subgroup.zpowers x = ⊥ := hU _ (by
    rintro _ ⟨k, rfl⟩
    exact hx k)
  simpa using hS

theorem eq_one_of_forall_pow_mem {G : Type*} [Group G] {U : Set G}
    (hU : NoSubgroupIn U) (hs : ∀ y ∈ U, y⁻¹ ∈ U) {x : G}
    (hx : ∀ n : ℕ, x ^ n ∈ U) : x = 1 := by
  refine eq_one_of_forall_zpow_mem hU fun k => ?_
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa using hx n
  · simpa using hs _ (hx n)

/-- The identity of p. 92. -/
theorem conj_eq_inv {G : Type*} [Group G] {x y : G} (h : x ^ 2 = y ^ 2) :
    y⁻¹ * (x * y⁻¹) * y = (x * y⁻¹)⁻¹ := by
  have h' : x * x = y * y := by simpa [pow_two] using h
  calc y⁻¹ * (x * y⁻¹) * y = y⁻¹ * x := by group
    _ = y⁻¹ * (x * x) * x⁻¹ := by group
    _ = y⁻¹ * (y * y) * x⁻¹ := by rw [h']
    _ = (x * y⁻¹)⁻¹ := by group

theorem conj_pow_eq_inv {G : Type*} [Group G] {x y : G} (h : x ^ 2 = y ^ 2) (k : ℕ) :
    y⁻¹ * (x * y⁻¹) ^ k * y = ((x * y⁻¹) ^ k)⁻¹ := by
  have hc := conj_eq_inv h
  have : (y⁻¹ * (x * y⁻¹) * y) ^ k = y⁻¹ * (x * y⁻¹) ^ k * y := by
    have := conj_pow (a := y⁻¹) (b := x * y⁻¹) (i := k)
    simpa using this
  rw [← this, hc, inv_pow]

/-- Theorem 3. -/
theorem square_injective {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [FirstCountableTopology G] {W : Set G} (hWc : IsCompact W) (hWn : W ∈ 𝓝 (1 : G))
    (hWs : ∀ y ∈ W, y⁻¹ ∈ W) (hW : NoSubgroupIn W) :
    ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, ∀ y ∈ U, x ^ 2 = y ^ 2 → x = y := by
  by_contra hcon
  simp only [not_exists, not_and, not_forall] at hcon
  obtain ⟨V, hV⟩ := (𝓝 (1 : G)).exists_antitone_basis
  have hex : ∀ i, ∃ x ∈ V i, ∃ y ∈ V i, x ^ 2 = y ^ 2 ∧ x ≠ y := by
    intro i
    obtain ⟨x, hx, y, hy, hsq, hne⟩ := hcon (V i) (hV.mem i)
    exact ⟨x, hx, y, hy, hsq, hne⟩
  choose x hx y hy hsq hne using hex
  have hxt : Tendsto x atTop (𝓝 1) := hV.tendsto hx
  have hyt : Tendsto y atTop (𝓝 1) := hV.tendsto hy
  set a : ℕ → G := fun i => x i * (y i)⁻¹ with ha
  have hat : Tendsto a atTop (𝓝 1) := by
    simpa using hxt.mul hyt.inv
  have ha1 : ∀ i, a i ≠ 1 := fun i h => hne i (by
    have : x i * (y i)⁻¹ = 1 := h
    exact mul_inv_eq_one.1 this)
  have hexit : ∀ i, ∃ n : ℕ, a i ^ n ∉ W := by
    intro i
    by_contra h
    simp only [not_exists, not_not] at h
    exact ha1 i (eq_one_of_forall_pow_mem hW hWs h)
  classical
  let n : ℕ → ℕ := fun i => Nat.find (hexit i)
  have hn : ∀ i, a i ^ n i ∉ W := fun i => Nat.find_spec (hexit i)
  have hmin : ∀ i, ∀ k < n i, a i ^ k ∈ W := fun i k hk => by
    have := Nat.find_min (hexit i) hk
    simpa using this
  have hone : (1 : G) ∈ W := mem_of_mem_nhds hWn
  have hn0 : ∀ i, n i ≠ 0 := fun i h0 => hn i (by rw [h0, pow_zero]; exact hone)
  set c : ℕ → G := fun i => a i ^ (n i - 1) with hc
  have hcW : ∀ i, c i ∈ W := fun i => hmin i _ (Nat.sub_lt (Nat.pos_of_ne_zero (hn0 i)) one_pos)
  have hca : ∀ i, c i * a i ∉ W := fun i => by
    have : c i * a i = a i ^ n i := by
      simp only [hc]
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero (hn0 i))]
    rw [this]
    exact hn i
  obtain ⟨b, hbW, φ, hφ, hlim⟩ := hWc.tendsto_subseq hcW
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hd : Tendsto (fun i => c (φ i) * a (φ i)) atTop (𝓝 b) := by
    simpa using hlim.mul (hat.comp hφt)
  have hb1 : b ≠ 1 := by
    rintro rfl
    obtain ⟨i, hi⟩ := (hd.eventually (mem_of_superset hWn fun _ h => h)).exists
    exact hca _ hi
  have hconj : Tendsto (fun i => (y (φ i))⁻¹ * c (φ i) * y (φ i)) atTop (𝓝 b) := by
    have h1 := (hyt.comp hφt).inv
    have h2 := h1.mul hlim
    have h3 := h2.mul (hyt.comp hφt)
    simpa using h3
  have hconj2 : Tendsto (fun i => (c (φ i))⁻¹) atTop (𝓝 b⁻¹) := hlim.inv
  have heq : (fun i => (y (φ i))⁻¹ * c (φ i) * y (φ i)) = fun i => (c (φ i))⁻¹ := by
    funext i
    exact conj_pow_eq_inv (hsq (φ i)) _
  rw [heq] at hconj
  have hbb : b = b⁻¹ := tendsto_nhds_unique hconj hconj2
  have hb2 : b * b = 1 := by
    nth_rewrite 1 [hbb]
    simp
  refine hb1 (eq_one_of_forall_zpow_mem hW fun k => ?_)
  have hsq2 : b ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hb2
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · rw [zpow_mul, hsq2, one_zpow]
    exact hone
  · rw [zpow_add, zpow_mul, hsq2, one_zpow, one_mul, zpow_one]
    exact hbW

/-- The one-parameter subgroup with `X(t) ∈ U` for `|t| ≤ 1` is determined by `X 1`. -/
theorem onePar_eq {G : Type*} [Group G] [TopologicalSpace G] [T2Space G] {U : Set G}
    (hU : ∀ x ∈ U, ∀ y ∈ U, x ^ 2 = y ^ 2 → x = y) {X Y : ℝ → G} (hXc : Continuous X)
    (hYc : Continuous Y) (hXa : ∀ s t, X (s + t) = X s * X t) (hYa : ∀ s t, Y (s + t) = Y s * Y t)
    (hXU : ∀ t, |t| ≤ 1 → X t ∈ U) (hYU : ∀ t, |t| ≤ 1 → Y t ∈ U) (h1 : X 1 = Y 1) : X = Y := by
  have hdy : ∀ k : ℕ, X ((1 / 2 : ℝ) ^ k) = Y ((1 / 2 : ℝ) ^ k) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      have ht : |(1 / 2 : ℝ) ^ (k + 1)| ≤ 1 := by
        rw [abs_of_pos (by positivity)]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      refine hU _ (hXU _ ht) _ (hYU _ ht) ?_
      have hs : (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ (k + 1) + (1 / 2 : ℝ) ^ (k + 1) := by
        rw [pow_succ]
        ring
      rw [pow_two, pow_two, ← hXa, ← hYa, ← hs, ih]
  -- integer multiples
  have hmul : ∀ (Z : ℝ → G), (∀ s t, Z (s + t) = Z s * Z t) → ∀ (t : ℝ) (m : ℤ),
      Z ((m : ℝ) * t) = Z t ^ m := by
    intro Z hZ t m
    have hZ0 : Z 0 = 1 := by
      have := hZ 0 0
      simpa using this
    induction m using Int.induction_on with
    | zero => simpa using hZ0
    | succ i ih =>
      have : ((((i : ℕ) : ℤ) + 1 : ℤ) : ℝ) * t = ((i : ℕ) : ℤ) * t + t := by
        push_cast
        ring
      rw [this, hZ, ih, zpow_add_one]
    | pred i ih =>
      have : ((-((i : ℕ) : ℤ) - 1 : ℤ) : ℝ) * t + t = (-((i : ℕ) : ℤ) : ℤ) * t := by
        push_cast
        ring
      have h2 := hZ (((-((i : ℕ) : ℤ) - 1 : ℤ) : ℝ) * t) t
      rw [this, ih] at h2
      rw [zpow_sub_one]
      rw [h2]
      group
  funext r
  -- the dyadic approximation of r
  let d : ℕ → ℝ := fun k => (⌊r * 2 ^ k⌋ : ℝ) * (1 / 2 : ℝ) ^ k
  have hdt : Tendsto d atTop (𝓝 r) := by
    have hl : Tendsto (fun k : ℕ => r - (1 / 2 : ℝ) ^ k) atTop (𝓝 r) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
        (by norm_num) (by norm_num)).const_sub r
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds ?_ ?_
    · intro k
      have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
      have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      have := (Int.lt_floor_add_one (r * 2 ^ k)).le
      have h3 := mul_le_mul_of_nonneg_right this hp.le
      have h4 : r * 2 ^ k * (1 / 2 : ℝ) ^ k = r := by rw [mul_assoc, h2, mul_one]
      rw [h4, add_mul, one_mul] at h3
      simp only [d]
      linarith
    · intro k
      have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
      have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      have := Int.floor_le (r * 2 ^ k)
      have h3 := mul_le_mul_of_nonneg_right this hp.le
      have h4 : r * 2 ^ k * (1 / 2 : ℝ) ^ k = r := by rw [mul_assoc, h2, mul_one]
      rw [h4] at h3
      simp only [d]
      linarith
  have hXd : Tendsto (fun k => X (d k)) atTop (𝓝 (X r)) := hXc.continuousAt.tendsto.comp hdt
  have hYd : Tendsto (fun k => Y (d k)) atTop (𝓝 (Y r)) := hYc.continuousAt.tendsto.comp hdt
  have heq : (fun k => X (d k)) = fun k => Y (d k) := by
    funext k
    simp only [d]
    rw [hmul X hXa, hmul Y hYa, hdy]
  rw [heq] at hXd
  exact tendsto_nhds_unique hXd hYd

end KaplanskyLie.SquaringNss

#print axioms KaplanskyLie.SquaringNss.conj_eq_inv
#print axioms KaplanskyLie.SquaringNss.conj_pow_eq_inv
#print axioms KaplanskyLie.SquaringNss.eq_one_of_forall_zpow_mem
#print axioms KaplanskyLie.SquaringNss.eq_one_of_forall_pow_mem
#print axioms KaplanskyLie.SquaringNss.square_injective
#print axioms KaplanskyLie.SquaringNss.onePar_eq
