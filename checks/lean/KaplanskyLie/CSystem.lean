import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# `C`-systems: integrality, theorems 62–65, theorem 67

Chapter I, § 6, pp. 58–63: axioms (2)–(5) of a `C`-system
(`step:c-system-negative`, `step:c-system-multiples`, `step:c-system-integer`,
`step:c-system-string`), the integrality of `2 (α, β) / (α, α)` for all pairs,
theorem 62 (`th:cartan-integers`), theorem 63 (`th:string-length`), theorem 64
(`th:proportional-roots`), theorem 65 (`th:reflection-invariance`) and theorem 67
(`th:positive-root-minus-simple`) with the added «не принадлежащий Δ»; the printed
form of theorem 67 is refuted.

Notation.  `K` is an ordered field (`Field K`, `LinearOrder K`, `IsStrictOrderedRing K`);
`V` a `K`-module; `B` a symmetric bilinear form, positive definite.  Axiom (1) is
only a normalisation and is not used.  Axioms (4) and (5) are one field `string` of
the structure, as in the printed text: for `β ≠ ±α`, `β - α ∉ Γ`, there is a natural
`r` with `r (α, α) = -2 (α, β)`, `β + i α ∈ Γ` for `i ≤ r`, `β + (r + 1) α ∉ Γ`.

* `CSystem`: the axioms.
* `exists_bottom`: the descent of p. 59 to `γ = β - m α` with `γ - α ∉ Γ`.
* `cartan_integer`: `2 (α, β) / (α, α)` is an integer for all roots.
* `PosDef.schwarz`, `PosDef.schwarz_eq`: `(α, β)² ≤ (α, α)(β, β)`; equality gives
  proportional vectors.
* `proportional`: theorem 64.
* `cartan_integers`: theorem 62, with the case of equality in Schwarz handled by
  theorem 64 (the question of the order of the proofs: not circular, `proportional`
  uses only `cartan_integer` and axiom (3)).
* `string_length`: theorem 63.
* `reflection_mem`: theorem 65, including `β = ±α`, where the formula for `r` of p. 60
  fails and axiom (2) is used.
* `positive_root_minus_simple`: theorem 67 with the added condition, in the sharper
  form that needs only `β = Σ m_i α_i` with `m_i ≥ 0`, `α_i ∈ Γ`, `β ≠ α_i`.
* `printed_theorem_67_false`: for `Γ = {±1}` in `ℚ`, `β = α = 1`, the printed statement
  fails.

Not covered: the classification, theorems 66, 68–72 (checked on all simple types of
rank at most 8 in `checks/sage/chapter-1c.py`).
-/

set_option linter.unusedSectionVars false

namespace KaplanskyLie.CSystem

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [AddCommGroup V] [Module K V]

/-- A symmetric positive definite bilinear form. -/
structure PosDef (B : V → V → K) : Prop where
  add_right : ∀ x y z, B x (y + z) = B x y + B x z
  smul_right : ∀ (c : K) x y, B x (c • y) = c * B x y
  symm : ∀ x y, B x y = B y x
  pos : ∀ x, x ≠ 0 → 0 < B x x

namespace PosDef

variable {B : V → V → K} (hB : PosDef B)
include hB

theorem add_left (x y z : V) : B (x + y) z = B x z + B y z := by
  rw [hB.symm, hB.add_right, hB.symm z x, hB.symm z y]

theorem smul_left (c : K) (x y : V) : B (c • x) y = c * B x y := by
  rw [hB.symm, hB.smul_right, hB.symm y x]

theorem neg_right (x y : V) : B x (-y) = - B x y := by
  have h := hB.smul_right (-1) x y
  simpa using h

theorem neg_left (x y : V) : B (-x) y = - B x y := by
  rw [hB.symm, hB.neg_right, hB.symm]

theorem natsmul_right (n : ℕ) (x y : V) : B x (n • y) = (n : K) * B x y := by
  rw [← Nat.cast_smul_eq_nsmul K n y, hB.smul_right]

theorem self_ne (x : V) (hx : x ≠ 0) : B x x ≠ 0 := (hB.pos x hx).ne'

theorem expand (s c : K) (a b : V) :
    B (s • b - c • a) (s • b - c • a) =
      s * (s * B b b) - 2 * s * c * B a b + c * (c * B a a) := by
  have e : s • b - c • a = s • b + (-c) • a := by module
  rw [e, hB.add_right, hB.add_left, hB.add_left, hB.smul_right, hB.smul_right, hB.smul_left,
    hB.smul_left, hB.smul_right, hB.smul_left, hB.smul_right, hB.smul_left, hB.symm b a]
  ring

/-- Cauchy–Schwarz in an ordered field. -/
theorem schwarz {a b : V} (ha : a ≠ 0) : B a b ^ 2 ≤ B a a * B b b := by
  have hs : 0 < B a a := hB.pos a ha
  by_cases hv : B a a • b - B a b • a = 0
  · have hb : B a a • b = B a b • a := sub_eq_zero.mp hv
    have h2 : B a a * B b b = B a b * B a b := by
      have h3 : B b (B a a • b) = B b (B a b • a) := by rw [hb]
      rw [hB.smul_right, hB.smul_right, hB.symm b a] at h3
      exact h3
    rw [h2]
    nlinarith
  · have hp := hB.pos _ hv
    rw [hB.expand] at hp
    have e : B a a * (B a a * B b b) - 2 * B a a * B a b * B a b + B a b * (B a b * B a a) =
        B a a * (B a a * B b b - B a b ^ 2) := by ring
    rw [e] at hp
    have h4 : 0 < B a a * B b b - B a b ^ 2 := (mul_pos_iff_of_pos_left hs).mp hp
    linarith

/-- Equality in Cauchy–Schwarz gives proportional vectors. -/
theorem schwarz_eq {a b : V} (h : B a b ^ 2 = B a a * B b b) :
    B a a • b = B a b • a := by
  by_contra hne
  have hv : B a a • b - B a b • a ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hp := hB.pos _ hv
  rw [hB.expand] at hp
  have e : B a a * (B a a * B b b) - 2 * B a a * B a b * B a b + B a b * (B a b * B a a) =
      B a a * (B a a * B b b - B a b ^ 2) := by ring
  rw [e, h] at hp
  simp only [sub_self, mul_zero, lt_self_iff_false] at hp

theorem sum_right {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → V) (x : V) :
    B x (∑ i ∈ s, m i • a i) = ∑ i ∈ s, (m i : K) * B x (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hB.smul_right 0 x 0
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hB.add_right, ih, hB.natsmul_right]

end PosDef

/-- Axioms (2)–(5) of a `C`-system. -/
structure IsCSystem (B : V → V → K) (Γ : Set V) : Prop where
  form : PosDef B
  finite : Γ.Finite
  ne_zero : (0 : V) ∉ Γ
  neg_mem : ∀ {α}, α ∈ Γ → -α ∈ Γ
  multiples : ∀ {α}, α ∈ Γ → ∀ m : ℤ, m • α ∈ Γ → m = 1 ∨ m = -1
  string : ∀ {α β}, α ∈ Γ → β ∈ Γ → β ≠ α → β ≠ -α → β - α ∉ Γ →
    ∃ r : ℕ, (r : K) * B α α = -2 * B α β ∧ (∀ i ≤ r, β + i • α ∈ Γ) ∧ β + (r + 1) • α ∉ Γ

variable {B : V → V → K} {Γ : Set V}

/-- `n (α, α) = 2 (α, β)`. -/
def IsCartan (B : V → V → K) (α β : V) (n : ℤ) : Prop := (n : K) * B α α = 2 * B α β

theorem ne_zero_of_mem (S : IsCSystem B Γ) {α : V} (h : α ∈ Γ) : α ≠ 0 :=
  fun e => S.ne_zero (e ▸ h)

/-- The roots `β - i α` do not stay in the finite set forever. -/
theorem exists_bottom (S : IsCSystem B Γ) {α β : V} (hα : α ∈ Γ) (hβ : β ∈ Γ) :
    ∃ m : ℕ, (∀ i ≤ m, β - i • α ∈ Γ) ∧ β - (m + 1) • α ∉ Γ := by
  by_contra hno
  push Not at hno
  have hall : ∀ m : ℕ, ∀ i ≤ m, β - i • α ∈ Γ := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have : i = 0 := by omega
      subst this
      simpa using hβ
    | succ m ih =>
      intro i hi
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · exact ih i (by omega)
      · have : i = m + 1 := by omega
        subst this
        exact hno m ih
  have hinj : Function.Injective (fun i : ℕ => β - i • α) := by
    intro i j hij
    have h1 : i • α = j • α := by simpa using hij
    have h2 : ((i : K) - (j : K)) • α = 0 := by
      rw [sub_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h1, sub_self]
    have h3 : (i : K) - (j : K) = 0 := by
      by_contra hne
      apply ne_zero_of_mem S hα
      have := inv_smul_smul₀ hne α
      rw [h2, smul_zero] at this
      exact this.symm
    exact_mod_cast sub_eq_zero.mp h3
  have hsub : Set.range (fun i : ℕ => β - i • α) ⊆ Γ := by
    rintro _ ⟨i, rfl⟩
    exact hall i i le_rfl
  have hfin : (Set.range (fun i : ℕ => β - i • α)).Finite := S.finite.subset hsub
  exact Set.infinite_range_of_injective hinj hfin

/-- A root that is a natural multiple `m α` of a root has `m = 1`. -/
theorem not_nat_multiple (S : IsCSystem B Γ) {α : V} (hα : α ∈ Γ) {m : ℕ}
    (hm : m • α ∈ Γ) : m = 1 := by
  have h := S.multiples hα (m : ℤ) (by rwa [natCast_zsmul])
  omega

/-- The bottom of the chain is not `± α` unless `β = ± α`. -/
theorem bottom_ne (S : IsCSystem B Γ) {α β : V} (hα : α ∈ Γ)
    (hβα : β ≠ α) (hβnα : β ≠ -α) {m : ℕ} (hm2 : ∀ i ≤ m, β - i • α ∈ Γ) :
    β - m • α ≠ α ∧ β - m • α ≠ -α := by
  have hβ : β ∈ Γ := by simpa using hm2 0 (Nat.zero_le _)
  constructor
  · intro e
    have hb : β = (m + 1) • α := by
      rw [sub_eq_iff_eq_add] at e
      rw [succ_nsmul, add_comm]
      exact e
    have hmem : (m + 1) • α ∈ Γ := by rwa [← hb]
    have := not_nat_multiple S hα hmem
    have hm0 : m = 0 := by omega
    subst hm0
    apply hβα
    simpa using hb
  · intro e
    have hb : β = m • α - α := by
      rw [sub_eq_iff_eq_add] at e
      rw [sub_eq_add_neg, add_comm]
      exact e
    cases m with
    | zero =>
      apply hβnα
      simpa using hb
    | succ k =>
      have hb2 : β = k • α := by
        rw [hb, succ_nsmul]; abel
      have hmem : k • α ∈ Γ := by rwa [← hb2]
      have := not_nat_multiple S hα hmem
      subst this
      apply hβα
      simpa using hb2

/-- Going up from the bottom of a chain through all the roots below `β`. -/
theorem chain_bound {α β : V} {m r t : ℕ}
    (hm : ∀ i ≤ m, β - i • α ∈ Γ) (hup : ∀ i ≤ t, β + i • α ∈ Γ)
    (htop : (β - m • α) + (r + 1) • α ∉ Γ) : m + t ≤ r := by
  by_contra hlt
  push Not at hlt
  apply htop
  rcases Nat.lt_or_ge (r + 1) (m + 1) with h | h
  · have e : (β - m • α) + (r + 1) • α = β - (m - (r + 1)) • α := by
      obtain ⟨d, rfl⟩ : ∃ d, m = (r + 1) + d := ⟨m - (r + 1), by omega⟩
      rw [Nat.add_sub_cancel_left, add_nsmul]
      abel
    rw [e]
    exact hm _ (by omega)
  · have e : (β - m • α) + (r + 1) • α = β + (r + 1 - m) • α := by
      obtain ⟨d, hd⟩ : ∃ d, r + 1 = m + d := ⟨r + 1 - m, by omega⟩
      rw [hd, Nat.add_sub_cancel_left, add_nsmul]
      abel
    rw [e]
    exact hup _ (by omega)

/-- Integrality for an arbitrary pair (p. 59). -/
theorem cartan_integer (S : IsCSystem B Γ) {α β : V} (hα : α ∈ Γ) (hβ : β ∈ Γ) :
    ∃ n : ℤ, IsCartan B α β n := by
  have hB := S.form
  by_cases h1 : β = α
  · subst h1
    exact ⟨2, by simp [IsCartan]⟩
  by_cases h2 : β = -α
  · subst h2
    refine ⟨-2, ?_⟩
    simp only [IsCartan, hB.neg_right]
    push_cast
    ring
  obtain ⟨m, hm, hm1⟩ := exists_bottom S hα hβ
  have hγmem : β - m • α ∈ Γ := hm m le_rfl
  have hγ1 : (β - m • α) - α ∉ Γ := by
    have e : (β - m • α) - α = β - (m + 1) • α := by rw [succ_nsmul]; abel
    rwa [e]
  obtain ⟨h3, h4⟩ := bottom_ne S hα h1 h2 hm
  obtain ⟨r, hr, -, -⟩ := S.string hα hγmem h3 h4 hγ1
  refine ⟨2 * m - r, ?_⟩
  have hbeta : B α β = B α (β - m • α) + (m : K) * B α α := by
    have e : β = (β - m • α) + m • α := by abel
    conv_lhs => rw [e, hB.add_right, hB.natsmul_right]
  simp only [IsCartan]
  push_cast
  rw [hbeta]
  linear_combination -hr

/-- `(m : ℤ) • x = (m : K) • x`. -/
theorem zsmul_eq (m : ℤ) (x : V) : m • x = (m : K) • x := (Int.cast_smul_eq_zsmul K m x).symm

/-- Theorem 64: a root proportional to a root `α` is `± α`. -/
theorem proportional (S : IsCSystem B Γ) {α β : V} (hα : α ∈ Γ) (hβ : β ∈ Γ) {c : K}
    (h : β = c • α) : c = 1 ∨ c = -1 := by
  have hB := S.form
  have hα0 := ne_zero_of_mem S hα
  have hβ0 := ne_zero_of_mem S hβ
  have hs := hB.self_ne α hα0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hβ0
    simpa using h
  obtain ⟨n, hn⟩ := cartan_integer S hα hβ
  obtain ⟨k, hk⟩ := cartan_integer S hβ hα
  simp only [IsCartan] at hn hk
  have hαβ : B α β = c * B α α := by rw [h, hB.smul_right]
  have hββ : B β β = c * (c * B α α) := by
    rw [h, hB.smul_right, hB.smul_left]
  have hβα : B β α = c * B α α := by rw [h, hB.smul_left]
  have e1 : (n : K) = 2 * c := by
    rw [hαβ] at hn
    have : ((n : K) - 2 * c) * B α α = 0 := by linear_combination hn
    have := (mul_eq_zero.mp this).resolve_right hs
    linarith
  have e2 : (k : K) * c = 2 := by
    rw [hββ, hβα] at hk
    have hne : c * B α α ≠ 0 := mul_ne_zero hc0 hs
    have : ((k : K) * c - 2) * (c * B α α) = 0 := by linear_combination hk
    have := (mul_eq_zero.mp this).resolve_right hne
    linarith
  have hnk : n * k = 4 := by
    have : ((n * k : ℤ) : K) = ((4 : ℤ) : K) := by
      push_cast
      rw [e1]
      linear_combination 2 * e2
    exact_mod_cast this
  have hd : n ∣ 4 := ⟨k, hnk.symm⟩
  have hle : n ≤ 4 := Int.le_of_dvd (by norm_num) hd
  have hge : -n ≤ 4 := Int.le_of_dvd (by norm_num) ((neg_dvd).mpr hd)
  have hcn : c = (n : K) / 2 := by rw [e1]; ring
  -- `α = 2 β` or `β = 2 α` up to sign, against axiom (3)
  have hmultα : ∀ m : ℤ, (m : K) = c → m = 1 ∨ m = -1 := by
    intro m hm
    apply S.multiples hα m
    rw [zsmul_eq (K := K), hm, ← h]
    exact hβ
  have hmultβ : ∀ m : ℤ, (m : K) * c = 1 → m = 1 ∨ m = -1 := by
    intro m hm
    apply S.multiples hβ m
    rw [zsmul_eq (K := K), h, smul_smul, hm, one_smul]
    exact hα
  have h2 : (2 : K) ≠ 0 := by norm_num
  have hcases : n = -4 ∨ n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2 ∨ n = 4 := by
    have hn3 : n ≠ 3 := by rintro rfl; omega
    have hnm3 : n ≠ -3 := by rintro rfl; omega
    have hn0 : n ≠ 0 := by rintro rfl; simp at hnk
    omega
  rcases hcases with e | e | e | e | e | e
  · have := hmultα (-2) (by rw [hcn, e]; push_cast; ring)
    omega
  · right
    rw [hcn, e]; push_cast; ring
  · have := hmultβ (-2) (by rw [hcn, e]; push_cast; ring)
    omega
  · have := hmultβ 2 (by rw [hcn, e]; push_cast; ring)
    omega
  · left
    rw [hcn, e]; push_cast; ring
  · have := hmultα 2 (by rw [hcn, e]; push_cast; ring)
    omega

/-- Theorem 62: `2 (α, β) / (α, α) = 0, ±1, ±2, ±3`. -/
theorem cartan_integers (S : IsCSystem B Γ) {α β : V} (hα : α ∈ Γ) (hβ : β ∈ Γ) {n : ℤ}
    (hn : IsCartan B α β n) :
    n = 0 ∨ n = 1 ∨ n = -1 ∨ n = 2 ∨ n = -2 ∨ n = 3 ∨ n = -3 := by
  have hB := S.form
  have hα0 := ne_zero_of_mem S hα
  have hβ0 := ne_zero_of_mem S hβ
  have ha := hB.pos α hα0
  have hb := hB.pos β hβ0
  obtain ⟨k, hk⟩ := cartan_integer S hβ hα
  simp only [IsCartan] at hn hk
  rw [hB.symm β α] at hk
  have hprod : ((n * k : ℤ) : K) * (B α α * B β β) = 4 * B α β ^ 2 := by
    push_cast
    linear_combination (B α β * 2) * hn + (n : K) * B α α * hk
  have hab : 0 < B α α * B β β := mul_pos ha hb
  have hsch := hB.schwarz (b := β) hα0
  have hle4 : n * k ≤ 4 := by
    have : ((n * k : ℤ) : K) ≤ ((4 : ℤ) : K) := by
      push_cast
      push_cast at hprod
      have h1 : ((n : K) * k) * (B α α * B β β) ≤ 4 * (B α α * B β β) := by
        rw [hprod]; linarith
      exact le_of_mul_le_mul_right h1 hab
    exact_mod_cast this
  have hge0 : 0 ≤ n * k := by
    have : ((0 : ℤ) : K) ≤ ((n * k : ℤ) : K) := by
      push_cast
      push_cast at hprod
      have h1 : 0 * (B α α * B β β) ≤ ((n : K) * k) * (B α α * B β β) := by
        rw [hprod, zero_mul]; positivity
      exact le_of_mul_le_mul_right h1 hab
    exact_mod_cast this
  rcases hle4.lt_or_eq with hlt | heq
  · -- `k = 0` gives `(α, β) = 0`, otherwise `|n| ≤ |n k| ≤ 3`
    by_cases hk0 : k = 0
    · left
      subst hk0
      have h0 : B α β = 0 := by
        simp only [Int.cast_zero, zero_mul] at hk
        linarith
      rw [h0] at hn
      have : (n : K) = 0 := by
        have := (mul_eq_zero.mp (hn.trans (by ring : (2 : K) * 0 = 0))).resolve_right ha.ne'
        exact this
      exact_mod_cast this
    · have hn3 : -3 ≤ n ∧ n ≤ 3 := by
        constructor
        · by_contra h
          push Not at h
          have hkneg : k < 0 := by
            by_contra hk1
            push Not at hk1
            have : 0 < k := lt_of_le_of_ne hk1 (Ne.symm hk0)
            nlinarith
          nlinarith
        · by_contra h
          push Not at h
          have hkpos : 0 < k := by
            by_contra hk1
            push Not at hk1
            have : k < 0 := lt_of_le_of_ne hk1 hk0
            nlinarith
          nlinarith
      omega
  · -- `n k = 4`: equality in Schwarz, so `β = ± α` by theorem 64
    have hsq : B α β ^ 2 = B α α * B β β := by
      rw [heq] at hprod
      push_cast at hprod
      linarith
    have hprop := hB.schwarz_eq hsq
    have hβe : β = (B α β / B α α) • α := by
      rw [div_eq_inv_mul, ← smul_smul, ← hprop, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    have hc := proportional S hα hβ hβe
    have hnval : (n : K) = 2 * (B α β / B α α) := by
      field_simp
      linarith
    rcases hc with hc | hc
    · have : (n : K) = ((2 : ℤ) : K) := by rw [hnval, hc]; push_cast; ring
      have : n = 2 := by exact_mod_cast this
      omega
    · have : (n : K) = ((-2 : ℤ) : K) := by rw [hnval, hc]; push_cast; ring
      have : n = -2 := by exact_mod_cast this
      omega

/-- Theorem 63: if `β, β + α, …, β + r α` are roots, then `r ≤ 3`. -/
theorem string_length (S : IsCSystem B Γ) {α β : V} (hα : α ∈ Γ) {r : ℕ}
    (hup : ∀ i ≤ r, β + i • α ∈ Γ) : r ≤ 3 := by
  have hβ : β ∈ Γ := by simpa using hup 0 (Nat.zero_le _)
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · omega
  have hone : β + α ∈ Γ := by simpa using hup 1 (by omega)
  have h1 : β ≠ α := by
    rintro rfl
    have hmem : 2 • β ∈ Γ := by rwa [two_nsmul]
    have := not_nat_multiple S hα hmem
    omega
  have h2 : β ≠ -α := by
    rintro rfl
    apply S.ne_zero
    simpa using hone
  obtain ⟨m, hm, hm1⟩ := exists_bottom S hα hβ
  have hγ1 : (β - m • α) - α ∉ Γ := by
    have e : (β - m • α) - α = β - (m + 1) • α := by rw [succ_nsmul]; abel
    rwa [e]
  obtain ⟨h3, h4⟩ := bottom_ne S hα h1 h2 hm
  obtain ⟨q, hq, -, hqtop⟩ := S.string hα (hm m le_rfl) h3 h4 hγ1
  have hbound := chain_bound hm hup hqtop
  have hcart : IsCartan B α (β - m • α) (-(q : ℤ)) := by
    simp only [IsCartan]
    push_cast
    linear_combination -hq
  have := cartan_integers S hα (hm m le_rfl) hcart
  omega

/-- Theorem 65: `Γ` is carried to itself by the reflection in `α`. -/
theorem reflection_mem (S : IsCSystem B Γ) {α β : V} (hα : α ∈ Γ) (hβ : β ∈ Γ) {n : ℤ}
    (hn : IsCartan B α β n) : β - n • α ∈ Γ := by
  have hB := S.form
  have hα0 := ne_zero_of_mem S hα
  have ha := hB.pos α hα0
  simp only [IsCartan] at hn
  have huniq : ∀ q : ℤ, (q : K) * B α α = 2 * B α β → q = n := by
    intro q hq
    have h1 : ((q : K) - n) * B α α = 0 := by linear_combination hq - hn
    have h2 := (mul_eq_zero.mp h1).resolve_right ha.ne'
    have : (q : K) = n := by linarith
    exact_mod_cast this
  by_cases h1 : β = α
  · subst h1
    have : n = 2 := (huniq 2 (by push_cast; ring)).symm
    subst this
    have e : β - (2 : ℤ) • β = -β := by
      rw [two_zsmul]; abel
    rw [e]
    exact S.neg_mem hα
  by_cases h2 : β = -α
  · subst h2
    have : n = -2 := (huniq (-2) (by rw [hB.neg_right]; push_cast; ring)).symm
    subst this
    have e : -α - (-2 : ℤ) • α = α := by
      rw [neg_zsmul, two_zsmul]; abel
    rw [e]
    exact hα
  obtain ⟨m, hm, hm1⟩ := exists_bottom S hα hβ
  have hγ1 : (β - m • α) - α ∉ Γ := by
    have e : (β - m • α) - α = β - (m + 1) • α := by rw [succ_nsmul]; abel
    rwa [e]
  obtain ⟨h3, h4⟩ := bottom_ne S hα h1 h2 hm
  obtain ⟨r, hr, hchain, htop⟩ := S.string hα (hm m le_rfl) h3 h4 hγ1
  have hup0 : ∀ i ≤ 0, β + i • α ∈ Γ := by
    intro i hi
    have : i = 0 := by omega
    subst this
    simpa using hβ
  have hbound := chain_bound hm hup0 htop
  have hbeta : B α β = B α (β - m • α) + (m : K) * B α α := by
    have e : β = (β - m • α) + m • α := by abel
    conv_lhs => rw [e, hB.add_right, hB.natsmul_right]
  have hnval : n = 2 * m - r := by
    symm
    apply huniq
    push_cast
    rw [hbeta]
    linear_combination -hr
  have e : β - n • α = (β - m • α) + (r - m) • α := by
    obtain ⟨d, rfl⟩ : ∃ d, r = m + d := ⟨r - m, by omega⟩
    rw [hnval, Nat.add_sub_cancel_left, ← natCast_zsmul, ← natCast_zsmul]
    push_cast
    rw [show (2 * (m : ℤ) - (m + d)) = m - d by ring, sub_zsmul]
    abel
  rw [e]
  exact hchain _ (by omega)

/-- Theorem 67 with the added condition `β ∉ Δ`: some `β - α_i` is a root.  The hypothesis
`m_i ≥ 0` is the natural `m i`; independence of the `α_i` is not needed. -/
theorem positive_root_minus_simple (S : IsCSystem B Γ) {ι : Type*} (s : Finset ι) (a : ι → V)
    (ha : ∀ i ∈ s, a i ∈ Γ) (m : ι → ℕ) {β : V} (hβ : β ∈ Γ)
    (hsum : β = ∑ i ∈ s, m i • a i) (hne : ∀ i ∈ s, β ≠ a i) : ∃ i ∈ s, β - a i ∈ Γ := by
  have hB := S.form
  by_contra hno
  push Not at hno
  have hle : ∀ i ∈ s, B β (a i) ≤ 0 := by
    intro i hi
    have hai := ha i hi
    have hpos := hB.pos _ (ne_zero_of_mem S hai)
    by_cases hneg : β = - a i
    · rw [hneg, hB.neg_left]
      linarith
    · obtain ⟨r, hr, -, -⟩ := S.string hai hβ (hne i hi) hneg (hno i hi)
      rw [hB.symm]
      have hr0 : (0 : K) ≤ r := Nat.cast_nonneg r
      have : 0 ≤ (r : K) * B (a i) (a i) := mul_nonneg hr0 hpos.le
      linarith
  have hsum2 : B β β = ∑ i ∈ s, (m i : K) * B β (a i) := by
    conv_lhs => rw [hsum]
    rw [hB.symm, hsum, hB.sum_right, ← hsum]
  have hle0 : B β β ≤ 0 := by
    rw [hsum2]
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hle i hi)
  exact absurd (hB.pos β (ne_zero_of_mem S hβ)) (not_lt.mpr hle0)

/-- The system `{±1}` in `ℚ`. -/
theorem smallest_system :
    IsCSystem (fun x y : ℚ => x * y) ({1, -1} : Set ℚ) where
  form :=
    { add_right := fun x y z => by ring
      smul_right := fun c x y => by simp only [smul_eq_mul]; ring
      symm := fun x y => by ring
      pos := fun x hx => mul_self_pos.mpr hx }
  finite := Set.toFinite _
  ne_zero := by norm_num
  neg_mem := by
    rintro α (rfl | rfl)
    · right; rfl
    · left; norm_num
  multiples := by
    rintro α (rfl | rfl) m hm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, zsmul_eq_mul, mul_one] at hm
      rcases hm with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, zsmul_eq_mul] at hm
      rcases hm with h | h
      · right
        have : (m : ℚ) = -1 := by linarith
        exact_mod_cast this
      · left
        have : (m : ℚ) = 1 := by linarith
        exact_mod_cast this
  string := by
    rintro α β (rfl | rfl) (rfl | rfl) h1 h2 _
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd (by norm_num) h2
    · exact absurd rfl h1

/-- The printed theorem 67 is false: in `Γ = {±1}`, `Δ = {1}`, `β = 1 = 1 · α_1` is positive
with a nonnegative integral expansion, and `β - α_1 = 0` is not in `Γ`. -/
theorem printed_theorem_67_false :
    ¬ ∀ (s : Finset Unit) (m : Unit → ℕ) (β : ℚ), β ∈ ({1, -1} : Set ℚ) →
      β = ∑ i ∈ s, m i • (1 : ℚ) → s = {()} → ∃ i ∈ s, β - 1 ∈ ({1, -1} : Set ℚ) := by
  intro h
  obtain ⟨_, _, hmem⟩ := h {()} (fun _ => 1) 1 (by simp) (by simp) rfl
  norm_num at hmem

end KaplanskyLie.CSystem

#print axioms KaplanskyLie.CSystem.PosDef.schwarz
#print axioms KaplanskyLie.CSystem.PosDef.schwarz_eq
#print axioms KaplanskyLie.CSystem.exists_bottom
#print axioms KaplanskyLie.CSystem.not_nat_multiple
#print axioms KaplanskyLie.CSystem.bottom_ne
#print axioms KaplanskyLie.CSystem.chain_bound
#print axioms KaplanskyLie.CSystem.cartan_integer
#print axioms KaplanskyLie.CSystem.proportional
#print axioms KaplanskyLie.CSystem.cartan_integers
#print axioms KaplanskyLie.CSystem.string_length
#print axioms KaplanskyLie.CSystem.reflection_mem
#print axioms KaplanskyLie.CSystem.positive_root_minus_simple
#print axioms KaplanskyLie.CSystem.smallest_system
#print axioms KaplanskyLie.CSystem.printed_theorem_67_false
