import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Identities and estimates for an isometric left action (Chapter II)

The book's `C` with `(a f)(x) = f(a⁻¹ x)` is abstracted here by a group `G` acting linearly on
a real vector space `V` by isometries (`hiso : ∀ g v, ‖g • v‖ = ‖v‖`).  Nothing else about
`C` is used in these steps of the book.

* `smul_mul_sub`: `m (a b f - f) = a {m (b f - f)} + m (a f - f)`: lemma 19 (p. 116), formula (19)
  (p. 123) and lemma 29 (p. 122).
* `norm_mul_smul_sub_le`: `‖a b f - f‖ ≤ ‖a f - f‖ + ‖b f - f‖` (p. 111).
* `norm_list_prod_smul_sub_le`, `norm_list_prod_le_length_mul`: the telescoping estimate;
  `exists_max_factor`: formula (17) with `a_i` a factor with the largest `‖a f - f‖`.
* `norm_pow_smul_sub_le`: `‖a^t f - f‖ ≤ t ‖a f - f‖` (the estimate on p. 123, lemma 30).
* `pow_smul_sub_eq_sum`: `a^d f - f = ∑_{t<d} a^t (a f - f)`.
* `shift_sum_identity`: formula (2).  `norm_shift_sum_le`: the bound `d ε` for the left side,
  which precedes (3).
* `quotient_sum_identity`: formula (21).
* `power_shift_expansion`: formula (30).  `norm_power_shift_sub_le`: the estimate for the
  expression after (30), which gives `τ = 0` in the proof of theorem 17.
* `telescoping_identity`: formula (27), the identity behind lemma 37, for `m ≥ 1`.

Not covered: the analysis around these identities (the limits in theorem 12, lemma 37, theorem 17).
All identities are also checked as formal identities in `checks/sage`.
-/

namespace KaplanskyLie.ProductEstimate

open Finset

variable {G V : Type*} [Group G]

section Algebra

variable [AddCommGroup V] [DistribMulAction G V]

/-- The identity of lemma 19, (19), lemma 29, with `m = 1`. -/
theorem mul_smul_sub (a b : G) (f : V) :
    (a * b) • f - f = a • (b • f - f) + (a • f - f) := by
  rw [mul_smul, smul_sub]
  abel

theorem pow_smul_sub_eq_sum (a : G) (f : V) (d : ℕ) :
    a ^ d • f - f = ∑ t ∈ range d, a ^ t • (a • f - f) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, ← ih, smul_sub, ← mul_smul, ← pow_succ, pow_succ']
    abel

end Algebra

section Module

variable [AddCommGroup V] [DistribMulAction G V] {R : Type*} [CommRing R] [Module R V]
  [SMulCommClass G R V]

theorem smul_mul_sub (m : R) (a b : G) (f : V) :
    m • ((a * b) • f - f) = a • (m • (b • f - f)) + m • (a • f - f) := by
  rw [mul_smul_sub, smul_add, smul_comm a m]

/-- Formula (2). -/
theorem shift_sum_identity (m : R) (a : G) (f g : V) (d : ℕ) :
    m • (a ^ d • f - f) - (d : R) • g =
      ∑ t ∈ range d, a ^ t • (m • (a • f - f) - g) + ∑ t ∈ range d, (a ^ t • g - g) := by
  have h1 : ∑ t ∈ range d, a ^ t • (m • (a • f - f) - g) =
      ∑ t ∈ range d, (m • (a ^ t • (a • f - f)) - a ^ t • g) := by
    refine sum_congr rfl fun t _ => ?_
    rw [smul_sub, smul_comm]
  have h2 : ∑ t ∈ range d, (a ^ t • g - g) = ∑ t ∈ range d, a ^ t • g - (d : R) • g := by
    rw [sum_sub_distrib]
    simp [Nat.cast_smul_eq_nsmul]
  rw [h1, h2, sum_sub_distrib, ← smul_sum, ← pow_smul_sub_eq_sum]
  abel

end Module

section Field

variable [AddCommGroup V] [DistribMulAction G V] [Module ℝ V] [SMulCommClass G ℝ V]

/-- Formula (21): `h = n s`, `X(k s) = a^k`, `a = X(s)`. -/
theorem quotient_sum_identity (a : G) (f D : V) {n : ℕ} (hn : 0 < n) (s : ℝ) :
    ((n : ℝ) * s)⁻¹ • (a ^ n • f - f) - D =
      ∑ k ∈ range n, (n : ℝ)⁻¹ • (a ^ k • D - D) +
        ∑ k ∈ range n, (n : ℝ)⁻¹ • a ^ k • (s⁻¹ • (a • f - f) - D) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h1 : ∑ k ∈ range n, (n : ℝ)⁻¹ • a ^ k • (s⁻¹ • (a • f - f) - D) =
      ((n : ℝ) * s)⁻¹ • (∑ k ∈ range n, a ^ k • (a • f - f)) -
        (n : ℝ)⁻¹ • ∑ k ∈ range n, a ^ k • D := by
    rw [smul_sum, smul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [smul_sub, smul_sub, smul_comm (a ^ k) s⁻¹, smul_smul, mul_inv]
  have h2 : ∑ k ∈ range n, (n : ℝ)⁻¹ • (a ^ k • D - D) =
      (n : ℝ)⁻¹ • ∑ k ∈ range n, a ^ k • D - D := by
    rw [← smul_sum, sum_sub_distrib, smul_sub]
    congr 1
    simp only [sum_const, card_range]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  rw [h1, h2, ← pow_smul_sub_eq_sum]
  abel

/-- Formula (30): `γ = n (a ψ - ψ)`. -/
theorem power_shift_expansion (a : G) (ψ τ : V) {n : ℕ} (hn : 0 < n) :
    a ^ n • ψ - ψ =
      (n : ℝ)⁻¹ • ∑ t ∈ range n, a ^ t • ((n : ℝ) • (a • ψ - ψ) - τ) +
        (n : ℝ)⁻¹ • ∑ t ∈ range n, (a ^ t • τ - τ) + τ := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h1 : ∑ t ∈ range n, a ^ t • ((n : ℝ) • (a • ψ - ψ) - τ) =
      (n : ℝ) • (a ^ n • ψ - ψ) - ∑ t ∈ range n, a ^ t • τ := by
    rw [pow_smul_sub_eq_sum a ψ n, smul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [smul_sub, smul_comm]
  have h2 : ∑ t ∈ range n, (a ^ t • τ - τ) = ∑ t ∈ range n, a ^ t • τ - (n : ℝ) • τ := by
    rw [sum_sub_distrib]
    simp [Nat.cast_smul_eq_nsmul]
  rw [h1, h2, ← smul_add]
  have h3 : (n : ℝ) • (a ^ n • ψ - ψ) - ∑ t ∈ range n, a ^ t • τ +
      (∑ t ∈ range n, a ^ t • τ - (n : ℝ) • τ) = (n : ℝ) • (a ^ n • ψ - ψ) - (n : ℝ) • τ := by
    abel
  rw [h3, ← smul_sub, smul_smul, inv_mul_cancel₀ hn', one_smul]
  abel

/-- Formula (27): `c = Y(1/m) X(1/m) = y x`, `Y(r/m) = y^r`, `X(-1/m) = x⁻¹`,
`X_(r/m)(1/m) = y^(-r) x y^r`, and `D r` stands for `D_(X_(r/m)) f`. -/
theorem telescoping_identity (x y : G) (f : V) (D : ℕ → V) {m : ℕ} (hm : 0 < m) :
    (y * x) ^ m • f - y ^ m • f =
      (m : ℝ)⁻¹ • ∑ r ∈ range m, ((y * x) ^ (m - r) * x⁻¹ * y ^ r) • D r +
        (m : ℝ)⁻¹ • ∑ r ∈ range m, ((y * x) ^ (m - r) * x⁻¹ * y ^ r) •
          ((m : ℝ) • (((y ^ r)⁻¹ * x * y ^ r) • f - f) - D r) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  set c := y * x with hc
  -- the telescoping: T r = c^(m-r) y^r f
  have hstep : ∀ r ∈ range m, (c ^ (m - r) * x⁻¹ * y ^ r) • (((y ^ r)⁻¹ * x * y ^ r) • f - f) =
      c ^ (m - r) • (y ^ r • f) - c ^ (m - (r + 1)) • (y ^ (r + 1) • f) := by
    intro r hr
    have hr' : r < m := mem_range.1 hr
    obtain ⟨k, hk⟩ : ∃ k, m - r = k + 1 := ⟨m - r - 1, by omega⟩
    have hk2 : m - (r + 1) = k := by omega
    rw [hk, hk2]
    have hcx : c * x⁻¹ = y := by rw [hc]; group
    have e1 : (c ^ (k + 1) * x⁻¹ * y ^ r) * ((y ^ r)⁻¹ * x * y ^ r) = c ^ (k + 1) * y ^ r := by
      group
    have e2 : c ^ (k + 1) * x⁻¹ * y ^ r = c ^ k * y ^ (r + 1) := by
      rw [pow_succ c k, mul_assoc (c ^ k), hcx, mul_assoc, pow_succ' y r]
    calc (c ^ (k + 1) * x⁻¹ * y ^ r) • (((y ^ r)⁻¹ * x * y ^ r) • f - f)
        = ((c ^ (k + 1) * x⁻¹ * y ^ r) * ((y ^ r)⁻¹ * x * y ^ r)) • f -
            (c ^ (k + 1) * x⁻¹ * y ^ r) • f := by rw [smul_sub, ← mul_smul]
      _ = (c ^ (k + 1) * y ^ r) • f - (c ^ k * y ^ (r + 1)) • f := by rw [e1, e2]
      _ = c ^ (k + 1) • (y ^ r • f) - c ^ k • (y ^ (r + 1) • f) := by rw [mul_smul, mul_smul]
  have hsum : ∑ r ∈ range m, (c ^ (m - r) * x⁻¹ * y ^ r) •
      (((y ^ r)⁻¹ * x * y ^ r) • f - f) = c ^ m • f - y ^ m • f := by
    rw [sum_congr rfl hstep]
    simpa using sum_range_sub' (fun r => c ^ (m - r) • (y ^ r • f)) m
  have hAB : ∀ r ∈ range m, (c ^ (m - r) * x⁻¹ * y ^ r) • D r +
      (c ^ (m - r) * x⁻¹ * y ^ r) • ((m : ℝ) • (((y ^ r)⁻¹ * x * y ^ r) • f - f) - D r) =
      (m : ℝ) • ((c ^ (m - r) * x⁻¹ * y ^ r) • (((y ^ r)⁻¹ * x * y ^ r) • f - f)) := by
    intro r _
    rw [smul_sub, smul_comm]
    abel
  rw [← smul_add, ← sum_add_distrib, sum_congr rfl hAB, ← smul_sum, hsum, smul_smul,
    inv_mul_cancel₀ hm', one_smul]

end Field

section Norm

variable [SeminormedAddCommGroup V] [DistribMulAction G V]

theorem norm_mul_smul_sub_le (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (a b : G) (f : V) :
    ‖(a * b) • f - f‖ ≤ ‖a • f - f‖ + ‖b • f - f‖ := by
  rw [mul_smul_sub]
  calc ‖a • (b • f - f) + (a • f - f)‖ ≤ ‖a • (b • f - f)‖ + ‖a • f - f‖ := norm_add_le _ _
    _ = ‖a • f - f‖ + ‖b • f - f‖ := by rw [hiso, add_comm]

theorem norm_list_prod_smul_sub_le (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (L : List G) (f : V) :
    ‖L.prod • f - f‖ ≤ (L.map fun a => ‖a • f - f‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact (norm_mul_smul_sub_le hiso a L.prod f).trans (by linarith)

theorem norm_list_prod_le_length_mul (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (L : List G)
    (f : V) {M : ℝ} (hM : ∀ a ∈ L, ‖a • f - f‖ ≤ M) :
    ‖L.prod • f - f‖ ≤ L.length * M := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons, List.length_cons]
    have h1 := norm_mul_smul_sub_le hiso a L.prod f
    have h2 := ih fun b hb => hM b (List.mem_cons_of_mem a hb)
    have h3 := hM a List.mem_cons_self
    push_cast
    linarith

/-- Formula (17): a factor with the largest `‖a f - f‖`. -/
theorem exists_max_factor (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (L : List G) (hL : L ≠ [])
    (f : V) : ∃ a ∈ L, ‖L.prod • f - f‖ ≤ L.length * ‖a • f - f‖ := by
  classical
  have hne : L.toFinset.Nonempty := List.toFinset_nonempty_iff L |>.2 hL
  obtain ⟨a, ha, hmax⟩ := L.toFinset.exists_max_image (fun a => ‖a • f - f‖) hne
  exact ⟨a, List.mem_toFinset.1 ha, norm_list_prod_le_length_mul hiso L f fun b hb =>
    hmax b (List.mem_toFinset.2 hb)⟩

/-- The estimate on p. 123. -/
theorem norm_pow_smul_sub_le (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (a : G) (f : V) (t : ℕ) :
    ‖a ^ t • f - f‖ ≤ t * ‖a • f - f‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ]
    have := norm_mul_smul_sub_le hiso (a ^ t) a f
    push_cast
    linarith

end Norm

section NormModule

variable [SeminormedAddCommGroup V] [DistribMulAction G V] [NormedSpace ℝ V]
  [SMulCommClass G ℝ V]

/-- The bound for the left side of (2) that leads to (3): if the two summands of (2) are bounded
termwise by `ε/2`, the left side is at most `d ε`. -/
theorem norm_shift_sum_le (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (m : ℝ) (a : G) (f g : V)
    (d : ℕ) {ε : ℝ} (h1 : ‖m • (a • f - f) - g‖ ≤ ε / 2)
    (h2 : ∀ t < d, ‖a ^ t • g - g‖ ≤ ε / 2) :
    ‖m • (a ^ d • f - f) - (d : ℝ) • g‖ ≤ d * ε := by
  rw [shift_sum_identity]
  have hA : ‖∑ t ∈ range d, a ^ t • (m • (a • f - f) - g)‖ ≤ d * (ε / 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ t ∈ range d, ‖a ^ t • (m • (a • f - f) - g)‖
        ≤ ∑ _t ∈ range d, ε / 2 := sum_le_sum fun t _ => by rw [hiso]; exact h1
      _ = d * (ε / 2) := by simp
  have hB : ‖∑ t ∈ range d, (a ^ t • g - g)‖ ≤ d * (ε / 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ t ∈ range d, ‖a ^ t • g - g‖
        ≤ ∑ _t ∈ range d, ε / 2 := sum_le_sum fun t ht => h2 t (mem_range.1 ht)
      _ = d * (ε / 2) := by simp
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ d * (ε / 2) + d * (ε / 2) := add_le_add hA hB
    _ = d * ε := by ring

/-- The estimate after (30): `‖a^n ψ - ψ - τ‖ ≤ 2 ε` when `γ` is within `ε` of `τ` and the
powers of `a` move `τ` by at most `ε`. -/
theorem norm_power_shift_sub_le (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (a : G) (ψ τ : V)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (h1 : ‖(n : ℝ) • (a • ψ - ψ) - τ‖ ≤ ε)
    (h2 : ∀ t < n, ‖a ^ t • τ - τ‖ ≤ ε) : ‖a ^ n • ψ - ψ - τ‖ ≤ 2 * ε := by
  have hn' : (0 : ℝ) < n := by positivity
  rw [power_shift_expansion a ψ τ hn, add_sub_cancel_right]
  have hA : ‖(n : ℝ)⁻¹ • ∑ t ∈ range n, a ^ t • ((n : ℝ) • (a • ψ - ψ) - τ)‖ ≤ ε := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hn'.le]
    rw [inv_mul_le_iff₀ hn']
    refine (norm_sum_le _ _).trans ?_
    calc ∑ t ∈ range n, ‖a ^ t • ((n : ℝ) • (a • ψ - ψ) - τ)‖
        ≤ ∑ _t ∈ range n, ε := sum_le_sum fun t _ => by rw [hiso]; exact h1
      _ = n * ε := by simp
  have hB : ‖(n : ℝ)⁻¹ • ∑ t ∈ range n, (a ^ t • τ - τ)‖ ≤ ε := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hn'.le]
    rw [inv_mul_le_iff₀ hn']
    refine (norm_sum_le _ _).trans ?_
    calc ∑ t ∈ range n, ‖a ^ t • τ - τ‖
        ≤ ∑ _t ∈ range n, ε := sum_le_sum fun t ht => h2 t (mem_range.1 ht)
      _ = n * ε := by simp
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε + ε := add_le_add hA hB
    _ = 2 * ε := by ring

end NormModule

end KaplanskyLie.ProductEstimate

#print axioms KaplanskyLie.ProductEstimate.mul_smul_sub
#print axioms KaplanskyLie.ProductEstimate.pow_smul_sub_eq_sum
#print axioms KaplanskyLie.ProductEstimate.smul_mul_sub
#print axioms KaplanskyLie.ProductEstimate.shift_sum_identity
#print axioms KaplanskyLie.ProductEstimate.quotient_sum_identity
#print axioms KaplanskyLie.ProductEstimate.power_shift_expansion
#print axioms KaplanskyLie.ProductEstimate.telescoping_identity
#print axioms KaplanskyLie.ProductEstimate.norm_mul_smul_sub_le
#print axioms KaplanskyLie.ProductEstimate.norm_list_prod_smul_sub_le
#print axioms KaplanskyLie.ProductEstimate.norm_list_prod_le_length_mul
#print axioms KaplanskyLie.ProductEstimate.exists_max_factor
#print axioms KaplanskyLie.ProductEstimate.norm_pow_smul_sub_le
#print axioms KaplanskyLie.ProductEstimate.norm_shift_sum_le
#print axioms KaplanskyLie.ProductEstimate.norm_power_shift_sub_le
