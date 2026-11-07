import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The step function `Δ` and the function `φ` (lemmas 3, 4, 6 of Chapter II)

Chapter II, § 4, pp. 102-104, § 5, p. 106, § 10, p. 135.

Notation.  `Q`, `U` are subsets of a group `G`; `QData Q U n` says: `1 ∈ Q`, `Q` symmetric, `Q ⊆ U`,
and `n` is the least number with `Q ^ n ⊄ U` (`step:integer-n`; `Q ^ j` is the set of products of
`j` elements, the pointwise power of `Mathlib`).  `lev Q n x` is the least `j < n` with
`x ∈ Q ^ j`, or `n` if there is none, and `Delta Q n x = lev Q n x / n`: this is the printed table of
`step:function-delta`, by `delta_one`, `delta_eq`, `delta_eq_one`.  No topology is used: the
statements hold for any group, as the proofs in the book show.

* `delta_of_not_mem`, `delta_nonneg`, `delta_le_one`, `delta_inv`, `delta_mul_le`,
  `abs_delta_mul_sub_le`: lemma 3, (a)-(e).
* `delta_one`, `one_div_le_delta`: `Δ` has a strict minimum at `1`, which is what the corrected
  sentence of `step:function-theta` says (the book's «как и `Δ`» is about `1 - Δ`).
* `phi θ` is the supremum in (4), for `θ` with values in `[0, 1]`.  `phi_eq_zero`, `phi_one`,
  `phi_nonneg`, `phi_le_one`, `phi_lt_one`, `abs_phi_mul_sub_le`: lemma 4, (a)-(c).
* `abs_phi_mul_right_sub_le`: lemma 6 in the sharp form: if `|θ(x a) - θ(x)| ≤ ε` for all `x`, then
  `|φ(x a) - φ(x)| ≤ ε` for all `x`.  The bound does not depend on `Q`, `U`, `n`.
* `n_le_of_subset`, `delta_le_of_subset`: the step `n' ≤ n`, `Δ' ≥ Δ` in the proof of lemma 43.

Not covered: the Haar integral defining `ψ` and the lemmas that use it (tested on finite groups and on
the line in `checks/sage/chapter-2b.py`), the existence of `θ`.
-/

namespace KaplanskyLie.DeltaFunction

open Set
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The data of step (i): `n` is the least number with `Q ^ n ⊄ U`. -/
structure QData (Q U : Set G) (n : ℕ) : Prop where
  one_mem : (1 : G) ∈ Q
  symm : ∀ x ∈ Q, x⁻¹ ∈ Q
  subset : Q ⊆ U
  pow_subset : ∀ j < n, Q ^ j ⊆ U
  exit : ¬ Q ^ n ⊆ U

open Classical in
/-- The level of `x`: the least `j < n` with `x ∈ Q ^ j`, or `n`. -/
noncomputable def lev (Q : Set G) (n : ℕ) (x : G) : ℕ :=
  if h : ∃ j, j < n ∧ x ∈ Q ^ j then Nat.find h else n

/-- The function `Δ` of step (ii). -/
noncomputable def Delta (Q : Set G) (n : ℕ) (x : G) : ℝ := (lev Q n x : ℝ) / n

section Lev

variable {Q U : Set G} {n : ℕ}

theorem lev_le (x : G) : lev Q n x ≤ n := by
  classical
  unfold lev
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem lev_le_of_mem {j : ℕ} {x : G} (hj : j < n) (hx : x ∈ Q ^ j) : lev Q n x ≤ j := by
  classical
  have h : ∃ j, j < n ∧ x ∈ Q ^ j := ⟨j, hj, hx⟩
  unfold lev
  rw [dite_eq_left h]
  exact Nat.find_min' h ⟨hj, hx⟩

theorem mem_pow_lev {x : G} (hx : lev Q n x < n) : x ∈ Q ^ lev Q n x := by
  classical
  by_cases h : ∃ j, j < n ∧ x ∈ Q ^ j
  · have e : lev Q n x = Nat.find h := by unfold lev; rw [dite_eq_left h]
    rw [e]
    exact (Nat.find_spec h).2
  · have e : lev Q n x = n := by unfold lev; rw [dite_eq_right h]
    omega

theorem lev_eq_of_forall {x : G} (h : ∀ j < n, x ∉ Q ^ j) : lev Q n x = n := by
  classical
  have h' : ¬ ∃ j, j < n ∧ x ∈ Q ^ j := by
    rintro ⟨j, hj, hx⟩
    exact h j hj hx
  unfold lev
  rw [dite_eq_right h']

theorem QData.n_pos (h : QData Q U n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    apply h.exit
    rw [pow_zero]
    rintro _ rfl
    exact h.subset h.one_mem
  · exact hn

theorem QData.one_lt (h : QData Q U n) : 1 < n := by
  have h0 := h.n_pos
  by_contra hn
  have : n = 1 := by omega
  subst this
  apply h.exit
  rw [pow_one]
  exact h.subset

theorem QData.inv_mem_pow (h : QData Q U n) {j : ℕ} {x : G} (hx : x ∈ Q ^ j) : x⁻¹ ∈ Q ^ j := by
  have hQ : Q⁻¹ = Q := by
    ext y
    constructor
    · intro hy
      have := h.symm _ (mem_inv.1 hy)
      simpa using this
    · intro hy
      exact mem_inv.2 (h.symm _ hy)
  have : (Q ^ j)⁻¹ = Q ^ j := by rw [← inv_pow, hQ]
  rw [← this]
  exact inv_mem_inv.2 hx

theorem lev_inv_le (h : QData Q U n) (x : G) : lev Q n x⁻¹ ≤ lev Q n x := by
  by_cases hl : lev Q n x < n
  · exact lev_le_of_mem hl (h.inv_mem_pow (mem_pow_lev hl))
  · have := lev_le (Q := Q) (n := n) x⁻¹
    omega

theorem lev_inv (h : QData Q U n) (x : G) : lev Q n x⁻¹ = lev Q n x := by
  refine le_antisymm (lev_inv_le h x) ?_
  simpa using lev_inv_le h x⁻¹

theorem lev_mul_le (x y : G) : lev Q n (x * y) ≤ lev Q n x + lev Q n y := by
  have h3 := lev_le (Q := Q) (n := n) (x * y)
  by_cases hx : lev Q n x < n
  · by_cases hy : lev Q n y < n
    · by_cases hs : lev Q n x + lev Q n y < n
      · refine lev_le_of_mem hs ?_
        rw [pow_add]
        exact mul_mem_mul (mem_pow_lev hx) (mem_pow_lev hy)
      · omega
    · have := lev_le (Q := Q) (n := n) y
      omega
  · have := lev_le (Q := Q) (n := n) x
    omega

theorem lev_of_mem (h : QData Q U n) {q : G} (hq : q ∈ Q) : lev Q n q ≤ 1 :=
  lev_le_of_mem h.one_lt (by simpa using hq)

theorem lev_one (h : QData Q U n) : lev Q n (1 : G) = 0 := by
  have : lev Q n (1 : G) ≤ 0 := lev_le_of_mem h.n_pos (by simp)
  omega

theorem one_le_lev (h : QData Q U n) {x : G} (hx : x ≠ 1) : 1 ≤ lev Q n x := by
  by_contra hl
  have h0 : lev Q n x = 0 := by omega
  have hlt : lev Q n x < n := by rw [h0]; exact h.n_pos
  have hm := mem_pow_lev hlt
  rw [h0, pow_zero] at hm
  exact hx hm

end Lev

section Delta

variable {Q U : Set G} {n : ℕ}

theorem delta_one (h : QData Q U n) : Delta Q n (1 : G) = 0 := by
  simp [Delta, lev_one h]

/-- The printed table: `Δ x = j/n` if `x ∈ Q ^ j`, `x ∉ Q ^ (j - 1)`, `j < n`. -/
theorem delta_eq (h : QData Q U n) {j : ℕ} {x : G} (hj : j < n) (hx : x ∈ Q ^ j)
    (hx' : ∀ i < j, x ∉ Q ^ i) : Delta Q n x = (j : ℝ) / n := by
  have h1 : lev Q n x ≤ j := lev_le_of_mem hj hx
  have h2 : j ≤ lev Q n x := by
    by_contra hlt
    have hl : lev Q n x < j := by omega
    exact hx' _ hl (mem_pow_lev (by omega))
  have _ := h
  simp [Delta, le_antisymm h1 h2]

/-- The last line of the table: `Δ x = 1` if `x ∉ Q ^ (n - 1)`. -/
theorem delta_eq_one (h : QData Q U n) {x : G} (hx : x ∉ Q ^ (n - 1)) : Delta Q n x = 1 := by
  have hn := h.n_pos
  have hl : lev Q n x = n := lev_eq_of_forall fun j hj hxj =>
    hx (pow_subset_pow_right h.one_mem (by omega) hxj)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp [Delta, hl, hn']

theorem one_div_le_delta (h : QData Q U n) {x : G} (hx : x ≠ 1) : 1 / (n : ℝ) ≤ Delta Q n x := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have h1 : (1 : ℝ) ≤ lev Q n x := by exact_mod_cast one_le_lev h hx
  exact div_le_div_of_nonneg_right h1 hn.le

/-- Lemma 3 (a). -/
theorem delta_of_not_mem (h : QData Q U n) {x : G} (hx : x ∉ U) : Delta Q n x = 1 := by
  have hl : lev Q n x = n := lev_eq_of_forall fun j hj hxj => hx (h.pow_subset j hj hxj)
  have hn : (n : ℝ) ≠ 0 := by
    have := h.n_pos
    positivity
  simp [Delta, hl, hn]

/-- Lemma 3 (b). -/
theorem delta_nonneg (x : G) : 0 ≤ Delta Q n x := by
  unfold Delta
  positivity

theorem delta_le_one (h : QData Q U n) (x : G) : Delta Q n x ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  unfold Delta
  rw [div_le_one hn]
  exact_mod_cast lev_le x

/-- Lemma 3 (c). -/
theorem delta_inv (h : QData Q U n) (x : G) : Delta Q n x⁻¹ = Delta Q n x := by
  simp [Delta, lev_inv h]

/-- Lemma 3 (d). -/
theorem delta_mul_le (h : QData Q U n) (x y : G) :
    Delta Q n (x * y) ≤ Delta Q n x + Delta Q n y := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  unfold Delta
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hn.le
  exact_mod_cast lev_mul_le x y

/-- Lemma 3 (e). -/
theorem abs_delta_mul_sub_le (h : QData Q U n) {q : G} (hq : q ∈ Q) (x : G) :
    |Delta Q n (q * x) - Delta Q n x| ≤ 1 / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have h1 : lev Q n (q * x) ≤ lev Q n x + 1 := by
    have := lev_mul_le (Q := Q) (n := n) q x
    have := lev_of_mem h hq
    omega
  have h2 : lev Q n x ≤ lev Q n (q * x) + 1 := by
    have e := lev_mul_le (Q := Q) (n := n) q⁻¹ (q * x)
    rw [inv_mul_cancel_left] at e
    have := lev_of_mem h (h.symm q hq)
    omega
  have h1' : (lev Q n (q * x) : ℝ) ≤ lev Q n x + 1 := by exact_mod_cast h1
  have h2' : (lev Q n x : ℝ) ≤ lev Q n (q * x) + 1 := by exact_mod_cast h2
  unfold Delta
  rw [← sub_div, abs_div, abs_of_pos hn]
  refine div_le_div_of_nonneg_right ?_ hn.le
  rw [abs_le]
  constructor <;> linarith

/-- The step `n' ≤ n` of lemma 43. -/
theorem n_le_of_subset {U' : Set G} {n' : ℕ} (h : QData Q U n) (h' : QData Q U' n')
    (hs : U' ⊆ U) : n' ≤ n := by
  by_contra hlt
  exact h.exit ((h'.pow_subset n (by omega)).trans hs)

/-- The step `Δ' ≥ Δ` of lemma 43. -/
theorem delta_le_of_subset {U' : Set G} {n' : ℕ} (h : QData Q U n) (h' : QData Q U' n')
    (hs : U' ⊆ U) (x : G) : Delta Q n x ≤ Delta Q n' x := by
  have hnn := n_le_of_subset h h' hs
  have hn' : (0 : ℝ) < n' := by exact_mod_cast h'.n_pos
  by_cases hl : lev Q n' x < n'
  · have h1 : lev Q n x ≤ lev Q n' x :=
      lev_le_of_mem (lt_of_lt_of_le hl hnn) (mem_pow_lev hl)
    have h1' : (lev Q n x : ℝ) ≤ lev Q n' x := by exact_mod_cast h1
    have h2 : (n' : ℝ) ≤ n := by exact_mod_cast hnn
    unfold Delta
    calc (lev Q n x : ℝ) / n ≤ (lev Q n' x : ℝ) / n :=
          div_le_div_of_nonneg_right h1' (by linarith)
      _ ≤ (lev Q n' x : ℝ) / n' :=
          div_le_div_of_nonneg_left (by positivity) hn' h2
  · have e : lev Q n' x = n' := le_antisymm (lev_le x) (by omega)
    have : Delta Q n' x = 1 := by
      simp [Delta, e, hn'.ne']
    rw [this]
    exact delta_le_one h x

end Delta

/-- If `f`, `g` are bounded above and pointwise `ε`-close, then so are their suprema. -/
theorem abs_ciSup_sub_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} {ε : ℝ}
    (hf : BddAbove (range f)) (hg : BddAbove (range g)) (h : ∀ i, |f i - g i| ≤ ε) :
    |iSup f - iSup g| ≤ ε := by
  rw [abs_le]
  constructor
  · have : iSup g ≤ iSup f + ε := ciSup_le fun i => by
      have h1 := le_ciSup hf i
      have h2 := (abs_le.1 (h i)).1
      linarith
    linarith
  · have : iSup f ≤ iSup g + ε := ciSup_le fun i => by
      have h1 := le_ciSup hg i
      have h2 := (abs_le.1 (h i)).2
      linarith
    linarith

section Phi

variable {Q U : Set G} {n : ℕ}

/-- The function `φ` of formula (4). -/
noncomputable def phi (Q : Set G) (n : ℕ) (θ : G → ℝ) (x : G) : ℝ :=
  ⨆ y : G, (1 - Delta Q n y) * θ (y⁻¹ * x)

variable {θ : G → ℝ}

theorem term_nonneg (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (y x : G) :
    0 ≤ (1 - Delta Q n y) * θ (y⁻¹ * x) :=
  mul_nonneg (by linarith [delta_le_one h y]) (h0 _)

theorem term_le_one (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1) (y x : G) :
    (1 - Delta Q n y) * θ (y⁻¹ * x) ≤ 1 := by
  have a := delta_nonneg (Q := Q) (n := n) y
  have b := delta_le_one h y
  have c := h1 (y⁻¹ * x)
  have d := h0 (y⁻¹ * x)
  nlinarith

theorem bdd_term (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1) (x : G) :
    BddAbove (range fun y => (1 - Delta Q n y) * θ (y⁻¹ * x)) :=
  ⟨1, by rintro _ ⟨y, rfl⟩; exact term_le_one h h0 h1 y x⟩

theorem phi_le_one (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1) (x : G) :
    phi Q n θ x ≤ 1 :=
  ciSup_le fun y => term_le_one h h0 h1 y x

theorem theta_le_phi (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1) (x : G) :
    θ x ≤ phi Q n θ x := by
  have := le_ciSup (bdd_term h h0 h1 x) 1
  unfold phi
  simpa [delta_one h] using this

theorem phi_nonneg (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1) (x : G) :
    0 ≤ phi Q n θ x :=
  (h0 x).trans (theta_le_phi h h0 h1 x)

/-- Lemma 4 (b): `φ(1) = 1`. -/
theorem phi_one (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1) (h2 : θ 1 = 1) :
    phi Q n θ 1 = 1 :=
  le_antisymm (phi_le_one h h0 h1 1) (by rw [← h2]; exact theta_le_phi h h0 h1 1)

/-- Lemma 4 (b): `φ` is proper. -/
theorem phi_lt_one (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1)
    (hp : ∀ x, x ≠ 1 → θ x < 1) {x : G} (hx : x ≠ 1) : phi Q n θ x < 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hM : max (1 - 1 / (n : ℝ)) (θ x) < 1 := by
    refine max_lt ?_ (hp x hx)
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  refine lt_of_le_of_lt (ciSup_le fun y => ?_) hM
  by_cases hy : y = 1
  · subst hy
    simp [delta_one h]
  · refine le_max_of_le_left ?_
    have a := one_div_le_delta h hy
    have b := delta_le_one h y
    have c := h1 (y⁻¹ * x)
    have d := h0 (y⁻¹ * x)
    have e : 0 ≤ 1 - Delta Q n y := by linarith
    nlinarith

/-- Lemma 4 (a). -/
theorem phi_eq_zero (h : QData Q U n) (h3 : ∀ x, x ∉ U → θ x = 0) {x : G} (hx : x ∉ U * U) :
    phi Q n θ x = 0 := by
  have : (fun y => (1 - Delta Q n y) * θ (y⁻¹ * x)) = fun _ => (0 : ℝ) := by
    funext y
    by_cases hy : y ∈ U
    · have : y⁻¹ * x ∉ U := fun hz => hx ⟨y, hy, y⁻¹ * x, hz, by simp⟩
      rw [h3 _ this, mul_zero]
    · rw [delta_of_not_mem h hy]
      simp
  unfold phi
  rw [this]
  simp

/-- Lemma 4 (c). -/
theorem abs_phi_mul_sub_le (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1) {q : G}
    (hq : q ∈ Q) (x : G) : |phi Q n θ (q * x) - phi Q n θ x| ≤ 1 / n := by
  have e : phi Q n θ (q * x) = ⨆ y : G, (1 - Delta Q n (q * y)) * θ (y⁻¹ * x) := by
    unfold phi
    refine ((Equiv.mulLeft q).iSup_congr fun y => ?_).symm
    simp [mul_assoc]
  rw [e]
  have hb : BddAbove (range fun y : G => (1 - Delta Q n (q * y)) * θ (y⁻¹ * x)) :=
    ⟨1, by
      rintro _ ⟨y, rfl⟩
      have := term_le_one h h0 h1 (q * y) (q * x)
      simpa [mul_assoc] using this⟩
  refine abs_ciSup_sub_le hb (bdd_term h h0 h1 x) fun y => ?_
  have hd := abs_delta_mul_sub_le h hq y
  have ht1 := h1 (y⁻¹ * x)
  have ht0 := h0 (y⁻¹ * x)
  have : (1 - Delta Q n (q * y)) * θ (y⁻¹ * x) - (1 - Delta Q n y) * θ (y⁻¹ * x) =
      -(Delta Q n (q * y) - Delta Q n y) * θ (y⁻¹ * x) := by ring
  rw [this, abs_mul, abs_neg, abs_of_nonneg ht0]
  have hn : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  calc |Delta Q n (q * y) - Delta Q n y| * θ (y⁻¹ * x)
      ≤ (1 / n) * 1 := mul_le_mul hd ht1 ht0 (by positivity)
    _ = 1 / n := by ring

/-- Lemma 6. -/
theorem abs_phi_mul_right_sub_le (h : QData Q U n) (h0 : ∀ x, 0 ≤ θ x) (h1 : ∀ x, θ x ≤ 1) {a : G}
    {ε : ℝ} (hθ : ∀ z, |θ (z * a) - θ z| ≤ ε) (x : G) :
    |phi Q n θ (x * a) - phi Q n θ x| ≤ ε := by
  refine abs_ciSup_sub_le (bdd_term h h0 h1 _) (bdd_term h h0 h1 _) fun y => ?_
  have e : (1 - Delta Q n y) * θ (y⁻¹ * (x * a)) - (1 - Delta Q n y) * θ (y⁻¹ * x) =
      (1 - Delta Q n y) * (θ (y⁻¹ * x * a) - θ (y⁻¹ * x)) := by
    rw [mul_assoc]
    ring
  rw [e, abs_mul, abs_of_nonneg (by linarith [delta_le_one h y])]
  have hz := hθ (y⁻¹ * x)
  have a0 := delta_nonneg (Q := Q) (n := n) y
  have b0 := delta_le_one h y
  have c0 := abs_nonneg (θ (y⁻¹ * x * a) - θ (y⁻¹ * x))
  nlinarith

end Phi

end KaplanskyLie.DeltaFunction

#print axioms KaplanskyLie.DeltaFunction.delta_one
#print axioms KaplanskyLie.DeltaFunction.delta_eq
#print axioms KaplanskyLie.DeltaFunction.delta_eq_one
#print axioms KaplanskyLie.DeltaFunction.one_div_le_delta
#print axioms KaplanskyLie.DeltaFunction.delta_of_not_mem
#print axioms KaplanskyLie.DeltaFunction.delta_nonneg
#print axioms KaplanskyLie.DeltaFunction.delta_le_one
#print axioms KaplanskyLie.DeltaFunction.delta_inv
#print axioms KaplanskyLie.DeltaFunction.delta_mul_le
#print axioms KaplanskyLie.DeltaFunction.abs_delta_mul_sub_le
#print axioms KaplanskyLie.DeltaFunction.n_le_of_subset
#print axioms KaplanskyLie.DeltaFunction.delta_le_of_subset
#print axioms KaplanskyLie.DeltaFunction.abs_ciSup_sub_le
#print axioms KaplanskyLie.DeltaFunction.phi_one
#print axioms KaplanskyLie.DeltaFunction.phi_nonneg
#print axioms KaplanskyLie.DeltaFunction.phi_le_one
#print axioms KaplanskyLie.DeltaFunction.phi_lt_one
#print axioms KaplanskyLie.DeltaFunction.phi_eq_zero
#print axioms KaplanskyLie.DeltaFunction.abs_phi_mul_sub_le
#print axioms KaplanskyLie.DeltaFunction.abs_phi_mul_right_sub_le
