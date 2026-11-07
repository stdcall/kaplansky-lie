import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# The sets `Q_i`: lemma 15, the hypothesis of theorem 13, and theorem 4 (Chapter II)

Chapter II, § 2, pp. 94, 96 (theorem 4 and the first step of theorem 7), § 6, p. 111 (theorem 13, lemma 15).

Notation.  `U` is a compact symmetric neighbourhood of `1` in a Hausdorff topological group, containing
no subgroup but `{1}` (squaring need not be injective on it: the book's remark on p. 93).
`Q U i` is the set of `x` with `x, x², ..., x^i ∈ U`.  The book's `i ≥ 1` are all `i` here.

* `Q_antitone`, `Q_mem_nhds`, `Q_isCompact`, `Q_subset_of_nhds`: lemma 15, first part: the `Q_i` form a
  decreasing fundamental sequence of compact neighbourhoods of `1`.  The proof by compactness
  replaces the book's limit point of a sequence, so that first countability is not needed.
* `exists_pow_subset`, `Q_pow_subset`: lemma 15, second part: for every `N`, `Q_i^N ⊆ U` for large `i`, i.e.
  `n_i → ∞`.
* `exists_exit_of_ne_one`: if `Q_i` contains `x ≠ 1`, then `Q_i^n ⊄ U` for some `n`, so that `n_i` exists.
  `no_exit_of_discrete`: if `{1}` is open, then for large `i` no `n_i` exists: the printed theorem 13
  is meaningless for a discrete `G`, and the word «недискретной» of the corrected reading is needed.
* `pow_floor_mem`: theorem 4, with first countability as a hypothesis (the book has metrizability
  by theorem 2).
* `tendsto_of_pow_floor`: if moreover `m_i → ∞`, then `a_i → 1`: this hypothesis of theorem 5 is what the proofs
  of theorem 7 and lemma 27 need and do not state.

Not covered: theorem 5 (one step of it is in `FloorSteps`), theorem 13 itself.
-/

namespace KaplanskyLie.QSetsFundamental

open Topology Filter Set
open scoped Pointwise

variable {G : Type*} [Group G]

/-- `{1}` is the only subgroup contained in `U`. -/
def NoSubgroupIn (U : Set G) : Prop :=
  ∀ S : Subgroup G, (S : Set G) ⊆ U → S = ⊥

theorem eq_one_of_forall_pow_mem {U : Set G} (hU : NoSubgroupIn U) (hs : ∀ y ∈ U, y⁻¹ ∈ U) {x : G}
    (hx : ∀ n : ℕ, x ^ n ∈ U) : x = 1 := by
  have hS : Subgroup.zpowers x = ⊥ := hU _ (by
    rintro _ ⟨k, rfl⟩
    obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
    · simpa using hx n
    · simpa using hs _ (hx n))
  simpa using hS

/-- The book's `Q_i`: `x, x², ..., x^i ∈ U`. -/
def Q (U : Set G) (i : ℕ) : Set G := {x | ∀ j, 1 ≤ j → j ≤ i → x ^ j ∈ U}

theorem Q_antitone (U : Set G) : Antitone (Q U) := fun _ _ hij _ hx j h1 hj =>
  hx j h1 (hj.trans hij)

/-- If `Q_i` contains `x ≠ 1`, then `n_i` exists. -/
theorem exists_exit_of_ne_one {U : Set G} (hU : NoSubgroupIn U) (hs : ∀ y ∈ U, y⁻¹ ∈ U) {i : ℕ}
    {x : G} (hx : x ∈ Q U i) (h1 : x ≠ 1) : ∃ n, ¬ (Q U i) ^ n ⊆ U := by
  have : ∃ n : ℕ, x ^ n ∉ U := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact h1 (eq_one_of_forall_pow_mem hU hs h)
  obtain ⟨n, hn⟩ := this
  exact ⟨n, fun hsub => hn (hsub (pow_mem_pow hx))⟩

/-- If `Q_i = {1}`, there is no `n_i`. -/
theorem no_exit_of_eq_one {U : Set G} {i : ℕ} (h1 : (1 : G) ∈ U) (hQ : Q U i = {1}) (n : ℕ) :
    (Q U i) ^ n ⊆ U := by
  rw [hQ]
  simpa using h1

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem Q_mem_nhds {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (i : ℕ) : Q U i ∈ 𝓝 (1 : G) := by
  have : (⋂ j ∈ Finset.range (i + 1), {x : G | 1 ≤ j → x ^ j ∈ U}) ⊆ Q U i := by
    intro x hx j h1 hj
    simp only [mem_iInter] at hx
    exact hx j (Finset.mem_range.2 (by omega)) h1
  refine mem_of_superset ((Filter.biInter_finset_mem _).2 fun j _ => ?_) this
  by_cases h1 : 1 ≤ j
  · have hc : ContinuousAt (fun x : G => x ^ j) 1 := (continuous_pow j).continuousAt
    have hm : (fun x : G => x ^ j) ⁻¹' U ∈ 𝓝 (1 : G) := hc (by simpa using hU)
    exact mem_of_superset hm fun x hx _ => hx
  · exact mem_of_superset univ_mem fun x _ h => absurd h h1

variable [T2Space G]

theorem Q_isCompact {U : Set G} (hc : IsCompact U) {i : ℕ} (hi : 1 ≤ i) : IsCompact (Q U i) := by
  have hsub : Q U i ⊆ U := fun x hx => by simpa using hx 1 le_rfl hi
  refine hc.of_isClosed_subset ?_ hsub
  have : Q U i = ⋂ j ∈ Finset.range (i + 1), {x : G | 1 ≤ j → x ^ j ∈ U} := by
    ext x
    simp only [Q, mem_iInter, Finset.mem_range]
    constructor
    · intro h j hj hj1
      exact h j hj1 (by omega)
    · intro h j h1 hj
      exact h j (by omega) h1
  rw [this]
  refine isClosed_biInter fun j _ => ?_
  by_cases h1 : 1 ≤ j
  · have : {x : G | 1 ≤ j → x ^ j ∈ U} = (fun x : G => x ^ j) ⁻¹' U := by
      ext x
      exact ⟨fun h => h h1, fun h _ => h⟩
    rw [this]
    exact hc.isClosed.preimage (continuous_pow j)
  · have : {x : G | 1 ≤ j → x ^ j ∈ U} = univ := by
      ext x
      exact ⟨fun _ => mem_univ _, fun _ h => absurd h h1⟩
    rw [this]
    exact isClosed_univ

/-- Lemma 15: the `Q_i` form a fundamental sequence. -/
theorem Q_subset_of_nhds {U : Set G} (hc : IsCompact U) (h1 : (1 : G) ∈ U)
    (hs : ∀ y ∈ U, y⁻¹ ∈ U) (hS : NoSubgroupIn U) {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ i, Q U i ⊆ W := by
  obtain ⟨V, hVW, hVo, hV1⟩ := mem_nhds_iff.1 hW
  by_contra hnot
  simp only [not_exists] at hnot
  have hne : (⋂ i : ℕ, (Q U (i + 1) \ V)).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun i => Q U (i + 1) \ V) ?_ ?_ ?_ ?_
    · intro i
      exact sdiff_subset_sdiff_left (Q_antitone U (Nat.le_succ _))
    · intro i
      have hnv : ¬ Q U (i + 1) ⊆ V := fun h => hnot (i + 1) (h.trans hVW)
      exact sdiff_nonempty.2 hnv
    · exact (Q_isCompact hc (by omega)).diff hVo
    · intro i
      exact (Q_isCompact hc (by omega)).isClosed.sdiff hVo
  obtain ⟨z, hz⟩ := hne
  have hmem : ∀ i : ℕ, z ∈ Q U (i + 1) \ V := fun i => mem_iInter.1 hz i
  have hpow : ∀ n : ℕ, z ^ n ∈ U := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h1
    · exact (hmem n).1 n hn (by omega)
  have : z = 1 := eq_one_of_forall_pow_mem hS hs hpow
  exact (hmem 0).2 (this ▸ hV1)

omit [T2Space G] in
/-- For every `N` a neighbourhood `W` of `1` has `W^N ⊆ U`. -/
theorem exists_pow_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (N : ℕ) :
    ∃ W ∈ 𝓝 (1 : G), W ^ N ⊆ U := by
  induction N generalizing U with
  | zero =>
    refine ⟨univ, univ_mem, ?_⟩
    rw [pow_zero]
    simpa using mem_of_mem_nhds hU
  | succ N ih =>
    obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset hU
    have hV : V ∈ 𝓝 (1 : G) := hVo.mem_nhds hV1
    obtain ⟨W, hW, hWN⟩ := ih hV
    refine ⟨W ∩ V, inter_mem hW hV, ?_⟩
    rw [pow_succ]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine hVV (mul_mem_mul (hWN ?_) hb.2)
    exact pow_subset_pow_left inter_subset_left ha

/-- Lemma 15: `n_i → ∞`. -/
theorem Q_pow_subset {U : Set G} (hc : IsCompact U) (hn : U ∈ 𝓝 (1 : G)) (hs : ∀ y ∈ U, y⁻¹ ∈ U)
    (hS : NoSubgroupIn U) (N : ℕ) : ∃ i₀, ∀ i ≥ i₀, (Q U i) ^ N ⊆ U := by
  obtain ⟨W, hW, hWN⟩ := exists_pow_subset hn N
  obtain ⟨i₀, hi₀⟩ := Q_subset_of_nhds hc (mem_of_mem_nhds hn) hs hS hW
  exact ⟨i₀, fun i hi => (pow_subset_pow_left ((Q_antitone U hi).trans hi₀)).trans hWN⟩

/-- For a discrete `G`, `Q_i = {1}` for large `i`, and no `n_i` exists. -/
theorem no_exit_of_discrete {U : Set G} (hc : IsCompact U) (h1 : (1 : G) ∈ U)
    (hs : ∀ y ∈ U, y⁻¹ ∈ U) (hS : NoSubgroupIn U) (hd : ({1} : Set G) ∈ 𝓝 (1 : G)) :
    ∃ i₀, ∀ i ≥ i₀, ∀ n, (Q U i) ^ n ⊆ U := by
  obtain ⟨i₀, hi₀⟩ := Q_subset_of_nhds hc h1 hs hS hd
  refine ⟨i₀, fun i hi n => ?_⟩
  have hsub : Q U i ⊆ {1} := (Q_antitone U hi).trans hi₀
  have hmem : (1 : G) ∈ Q U i := fun j _ _ => by simpa using h1
  have hQ : Q U i = {1} := Subset.antisymm hsub (singleton_subset_iff.2 hmem)
  exact no_exit_of_eq_one h1 hQ n

variable [FirstCountableTopology G]

/-- Theorem 4. -/
theorem pow_floor_mem {U : Set G} (hc : IsCompact U) (hn : U ∈ 𝓝 (1 : G)) (hs : ∀ y ∈ U, y⁻¹ ∈ U)
    (hS : NoSubgroupIn U) (a : ℕ → G) (m : ℕ → ℕ)
    (ha : ∀ i j, 1 ≤ j → j ≤ m i → a i ^ j ∈ U) {V : Set G} (hV : V ∈ 𝓝 (1 : G)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ i, ∀ r : ℝ, 0 ≤ r → r < r₀ → a i ^ ⌊r * m i⌋₊ ∈ V := by
  by_contra hcon
  simp only [not_exists, not_and, not_forall] at hcon
  have h1U : (1 : G) ∈ U := mem_of_mem_nhds hn
  have hex : ∀ k : ℕ, ∃ i, ∃ r : ℝ, 0 ≤ r ∧ r < 1 / ((k : ℝ) + 1) ∧ a i ^ ⌊r * m i⌋₊ ∉ V := by
    intro k
    obtain ⟨i, r, hr, hrk, hnot⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨i, r, hr, hrk, hnot⟩
  choose i r hr0 hrk hnot using hex
  set c : ℕ → G := fun k => a (i k) ^ ⌊r k * m (i k)⌋₊ with hcdef
  -- p [r m] ≤ m when p r ≤ 1
  have hmem : ∀ (k p : ℕ), p ≤ k + 1 → c k ^ p ∈ U := by
    intro k p hp
    simp only [hcdef]
    rw [← pow_mul]
    have hpr : (p : ℝ) * r k ≤ 1 := by
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hpk : (p : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hp
      have hrk' := (hrk k).le
      calc (p : ℝ) * r k ≤ ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) :=
            mul_le_mul hpk hrk' (hr0 k) hk.le
        _ = 1 := by field_simp
    have hexp : ⌊r k * m (i k)⌋₊ * p ≤ m (i k) := by
      have h1 : (⌊r k * m (i k)⌋₊ : ℝ) ≤ r k * m (i k) := Nat.floor_le (by
        have := hr0 k
        positivity)
      have hp0 : (0 : ℝ) ≤ p := by positivity
      have hm0 : (0 : ℝ) ≤ m (i k) := by positivity
      have h2 : (⌊r k * m (i k)⌋₊ : ℝ) * p ≤ m (i k) := by
        calc (⌊r k * m (i k)⌋₊ : ℝ) * p ≤ (r k * m (i k)) * p :=
              mul_le_mul_of_nonneg_right h1 hp0
          _ = ((p : ℝ) * r k) * m (i k) := by ring
          _ ≤ 1 * m (i k) := mul_le_mul_of_nonneg_right hpr hm0
          _ = m (i k) := one_mul _
      exact_mod_cast h2
    rcases Nat.eq_zero_or_pos (⌊r k * m (i k)⌋₊ * p) with h0 | hpos
    · rw [h0, pow_zero]
      exact h1U
    · exact ha _ _ hpos hexp
  have hcU : ∀ k, c k ∈ U := fun k => by
    have := hmem k 1 (by omega)
    simpa using this
  obtain ⟨b, _, φ, hφ, hlim⟩ := hc.tendsto_subseq hcU
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hb1 : b ≠ 1 := by
    rintro rfl
    obtain ⟨k, hk⟩ := (hlim.eventually (mem_of_superset hV fun _ h => h)).exists
    exact hnot _ hk
  refine hb1 (eq_one_of_forall_pow_mem hS hs fun p => ?_)
  have hpow : Tendsto (fun k => c (φ k) ^ p) atTop (𝓝 (b ^ p)) := hlim.pow p
  refine hc.isClosed.mem_of_tendsto hpow ?_
  have hev : ∀ᶠ k in atTop, p ≤ φ k + 1 := by
    have := hφt.eventually (eventually_ge_atTop p)
    exact this.mono fun k hk => by omega
  exact hev.mono fun k hk => hmem _ _ hk

/-- The hypothesis `a_i → 1` used in theorem 7 and lemma 27 follows from theorem 4. -/
theorem tendsto_of_pow_floor {U : Set G} (hc : IsCompact U) (hn : U ∈ 𝓝 (1 : G))
    (hs : ∀ y ∈ U, y⁻¹ ∈ U) (hS : NoSubgroupIn U) (a : ℕ → G) (m : ℕ → ℕ)
    (ha : ∀ i j, 1 ≤ j → j ≤ m i → a i ^ j ∈ U) (hm : Tendsto m atTop atTop) :
    Tendsto a atTop (𝓝 1) := by
  rw [tendsto_def]
  intro V hV
  obtain ⟨r₀, hr₀, hprop⟩ := pow_floor_mem hc hn hs hS a m ha hV
  have hev : ∀ᶠ i in atTop, 1 / r₀ < (m i : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hm).eventually (eventually_gt_atTop _)
  refine mem_of_superset hev fun i hi => ?_
  have hi' : 1 / r₀ < (m i : ℝ) := hi
  have hmpos : (0 : ℝ) < m i := lt_trans (by positivity) hi'
  have hlt : 1 / (m i : ℝ) < r₀ := by
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hr₀] at hi'
    linarith
  have := hprop i (1 / (m i : ℝ)) (by positivity) hlt
  have e : ⌊1 / (m i : ℝ) * m i⌋₊ = 1 := by
    rw [one_div, inv_mul_cancel₀ hmpos.ne']
    simp
  rw [e, pow_one] at this
  exact this

end Topological

end KaplanskyLie.QSetsFundamental

#print axioms KaplanskyLie.QSetsFundamental.eq_one_of_forall_pow_mem
#print axioms KaplanskyLie.QSetsFundamental.Q_antitone
#print axioms KaplanskyLie.QSetsFundamental.exists_exit_of_ne_one
#print axioms KaplanskyLie.QSetsFundamental.no_exit_of_eq_one
#print axioms KaplanskyLie.QSetsFundamental.Q_mem_nhds
#print axioms KaplanskyLie.QSetsFundamental.Q_isCompact
#print axioms KaplanskyLie.QSetsFundamental.Q_subset_of_nhds
#print axioms KaplanskyLie.QSetsFundamental.exists_pow_subset
#print axioms KaplanskyLie.QSetsFundamental.Q_pow_subset
#print axioms KaplanskyLie.QSetsFundamental.no_exit_of_discrete
#print axioms KaplanskyLie.QSetsFundamental.pow_floor_mem
#print axioms KaplanskyLie.QSetsFundamental.tendsto_of_pow_floor
