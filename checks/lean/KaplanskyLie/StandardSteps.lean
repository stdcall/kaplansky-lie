import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Steps of §§ 8, 9 of Chapter II: lemmas 28, 30, 33

Chapter II, § 8, p. 120 (lemma 28, the numbers `λ_i`), § 9, pp. 122-124 (lemma 30, lemma 33).

* `pow_mem_of_tendsto_zero`: the first half of the proof of lemma 30.  `f` is an element of a normed
  space `V` on which `G` acts by isometries, `a ↦ a f` is continuous (theorem 11) and `a f = f`
  implies `a = 1` (`f` proper).  If `a_i → 1` and `m_i ‖a_i f - f‖ → 0`, then `a_i, ..., a_i^(m_i) ∈ U`
  for large `i`.  `U` is a compact neighbourhood of `1`; first countability replaces the book's
  metrizability (theorem 2).
* `exists_boundary_time`: the existence of `λ_i` in lemma 28: for a continuous `X : ℝ → G`, `X 0 = 1`, a
  closed `U` with `1` in its interior and `X t ∉ U`, `t > 0`, there is `0 < λ < t` with `X s ∈ U` for
  `0 ≤ s ≤ λ` and `X λ` on the boundary of `U`.
* `pow_eq_of_add`, `mem_Q_of_scale`: the computation in the proof of lemma 33: `X(t)^j = X(j t)`, hence
  `X(t) ∈ Q_i` if `X(u) ∈ U` for `|u| ≤ s` and `|t| ≤ s/i`.

Not covered: the second half of the proof of lemma 30 (it is theorem 12 and lemma 21), the other lemmas.
-/

namespace KaplanskyLie.StandardSteps

open Topology Filter Set

variable {G : Type*} [Group G]

theorem norm_pow_smul_sub_le {V : Type*} [SeminormedAddCommGroup V] [DistribMulAction G V]
    (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (a : G) (f : V) (t : ℕ) :
    ‖a ^ t • f - f‖ ≤ t * ‖a • f - f‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : a ^ (t + 1) • f - f = a ^ t • (a • f - f) + (a ^ t • f - f) := by
      rw [pow_succ, mul_smul, smul_sub]
      abel
    rw [h1]
    have h2 : ‖a ^ t • (a • f - f) + (a ^ t • f - f)‖ ≤ ‖a • f - f‖ + ‖a ^ t • f - f‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [hiso]
    push_cast
    linarith

variable [TopologicalSpace G]

/-- The first half of the proof of lemma 30. -/
theorem pow_mem_of_tendsto_zero [IsTopologicalGroup G] [T2Space G] [FirstCountableTopology G]
    {V : Type*} [SeminormedAddCommGroup V] [T0Space V] [DistribMulAction G V]
    (hiso : ∀ (g : G) (v : V), ‖g • v‖ = ‖v‖) (f : V) (hcont : Continuous fun a : G => a • f)
    (hprop : ∀ a : G, a • f = f → a = 1) {U : Set G} (hc : IsCompact U) (hn : U ∈ 𝓝 (1 : G))
    {a : ℕ → G} {m : ℕ → ℕ} (ha : Tendsto a atTop (𝓝 1))
    (h : Tendsto (fun i => (m i : ℝ) * ‖a i • f - f‖) atTop (𝓝 0)) :
    ∀ᶠ i in atTop, ∀ t ≤ m i, a i ^ t ∈ U := by
  by_contra hnot
  rw [not_eventually] at hnot
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hnot
  have h1U : (1 : G) ∈ U := mem_of_mem_nhds hn
  classical
  have hex : ∀ k, ∃ t, a (φ k) ^ t ∉ U ∧ t ≤ m (φ k) := by
    intro k
    have := hP k
    simp only [not_forall, exists_prop] at this
    obtain ⟨t, ht, hnotU⟩ := this
    exact ⟨t, hnotU, ht⟩
  let t : ℕ → ℕ := fun k => Nat.find (hex k)
  have ht1 : ∀ k, a (φ k) ^ t k ∉ U := fun k => (Nat.find_spec (hex k)).1
  have htm : ∀ k, t k ≤ m (φ k) := fun k => (Nat.find_spec (hex k)).2
  have ht0 : ∀ k, t k ≠ 0 := fun k h0 => ht1 k (by rw [h0, pow_zero]; exact h1U)
  have hmin : ∀ k, a (φ k) ^ (t k - 1) ∈ U := by
    intro k
    by_contra hk
    have hlt : t k - 1 < t k := Nat.sub_lt (Nat.pos_of_ne_zero (ht0 k)) one_pos
    exact Nat.find_min (hex k) hlt ⟨hk, (Nat.sub_le _ _).trans (htm k)⟩
  obtain ⟨b, _, ψ, hψ, hlim⟩ := hc.tendsto_subseq hmin
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have ha2 : Tendsto (fun k => a (φ (ψ k))) atTop (𝓝 1) := ha.comp (hφt.comp hψt)
  have hmul : Tendsto (fun k => a (φ (ψ k)) ^ t (ψ k)) atTop (𝓝 b) := by
    have h2 := hlim.mul ha2
    simp only [mul_one] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp]
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero (ht0 _))]
  -- b f = f
  have hsmul : Tendsto (fun k => a (φ (ψ k)) ^ t (ψ k) • f) atTop (𝓝 (b • f)) :=
    (hcont.tendsto b).comp hmul
  have hnorm0 : Tendsto (fun k => ‖a (φ (ψ k)) ^ t (ψ k) • f - f‖) atTop (𝓝 0) := by
    have hm : Tendsto (fun k => (m (φ (ψ k)) : ℝ) * ‖a (φ (ψ k)) • f - f‖) atTop (𝓝 0) :=
      h.comp (hφt.comp hψt)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hm
    refine (norm_pow_smul_sub_le hiso _ f _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact_mod_cast htm _
  have hf : Tendsto (fun k => a (φ (ψ k)) ^ t (ψ k) • f) atTop (𝓝 f) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hnorm0
  have hbf : b • f = f := tendsto_nhds_unique hsmul hf
  have hb1 : b = 1 := hprop b hbf
  rw [hb1] at hmul
  obtain ⟨k, hk⟩ := (hmul.eventually (mem_of_superset hn fun _ h => h)).exists
  exact ht1 _ hk

/-- The existence of `λ_i` in lemma 28. -/
theorem exists_boundary_time {X : ℝ → G} (hX : Continuous X) (h0 : X 0 = 1) {U : Set G}
    (hU : IsClosed U) (h1 : (1 : G) ∈ interior U) {t : ℝ} (ht : 0 < t) (hnot : X t ∉ U) :
    ∃ l : ℝ, 0 < l ∧ l < t ∧ (∀ s, 0 ≤ s → s ≤ l → X s ∈ U) ∧ X l ∈ U ∧ X l ∉ interior U := by
  let T : Set ℝ := {s | 0 ≤ s ∧ X s ∉ U}
  have hTne : T.Nonempty := ⟨t, ht.le, hnot⟩
  have hTb : BddBelow T := ⟨0, fun s hs => hs.1⟩
  let l := sInf T
  have hopenU : IsOpen (X ⁻¹' Uᶜ) := hU.isOpen_compl.preimage hX
  have hint : IsOpen (X ⁻¹' interior U) := isOpen_interior.preimage hX
  -- l > 0
  have h00 : (0 : ℝ) ∈ X ⁻¹' interior U := by
    simpa [mem_preimage, h0] using h1
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.1 hint 0 h00
  have hlower : ∀ s ∈ T, d ≤ s := by
    intro s hs
    by_contra hlt
    have hs' : s ∈ Metric.ball (0 : ℝ) d := by
      rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact not_le.1 hlt
    exact hs.2 (interior_subset (hball hs'))
  have hlpos : 0 < l := lt_of_lt_of_le hd (le_csInf hTne hlower)
  -- below l we are in U
  have hbelow : ∀ s, 0 ≤ s → s < l → X s ∈ U := by
    intro s hs0 hsl
    by_contra hnotU
    exact absurd (csInf_le hTb ⟨hs0, hnotU⟩ : l ≤ s) (not_le.2 hsl)
  -- l is not in T
  have hlU : X l ∈ U := by
    by_contra hnotU
    obtain ⟨e, he, hb⟩ := Metric.isOpen_iff.1 hopenU l hnotU
    have hs0 : 0 ≤ l - min (e / 2) (l / 2) := by
      have := min_le_right (e / 2) (l / 2)
      linarith
    have hmpos : 0 < min (e / 2) (l / 2) := lt_min (by positivity) (by positivity)
    have hsl : l - min (e / 2) (l / 2) < l := by linarith
    have hsb : l - min (e / 2) (l / 2) ∈ Metric.ball l e := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
      have h2 : l - (l - min (e / 2) (l / 2)) = min (e / 2) (l / 2) := by ring
      rw [h2, abs_of_pos hmpos]
      have := min_le_left (e / 2) (l / 2)
      linarith
    exact hb hsb (hbelow _ hs0 hsl)
  have hlt : l < t := by
    have hl_le : l ≤ t := csInf_le hTb ⟨ht.le, hnot⟩
    refine lt_of_le_of_ne hl_le ?_
    intro e
    exact hnot (e ▸ hlU)
  have hbdry : X l ∉ interior U := by
    intro hi
    obtain ⟨e, he, hb⟩ := Metric.isOpen_iff.1 hint l hi
    obtain ⟨s, hsT, hsl⟩ := exists_lt_of_csInf_lt hTne (by linarith : l < l + e)
    have hls : l ≤ s := csInf_le hTb hsT
    have hsb : s ∈ Metric.ball l e := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    exact hsT.2 (interior_subset (hb hsb))
  refine ⟨l, hlpos, hlt, fun s hs0 hsl => ?_, hlU, hbdry⟩
  rcases lt_or_eq_of_le hsl with h | h
  · exact hbelow s hs0 h
  · rw [h]
    exact hlU

omit [TopologicalSpace G] in
/-- `X(t)^j = X(j t)`. -/
theorem pow_eq_of_add {X : ℝ → G} (hX : ∀ s t, X (s + t) = X s * X t) (t : ℝ) (j : ℕ) :
    X t ^ j = X (j * t) := by
  have h0 : X 0 = 1 := by
    have := hX 0 0
    simpa using this
  induction j with
  | zero => simp [h0]
  | succ j ih =>
    rw [pow_succ, ih, ← hX]
    congr 1
    push_cast
    ring

omit [TopologicalSpace G] in
/-- The computation in the proof of lemma 33. -/
theorem mem_Q_of_scale {X : ℝ → G} (hX : ∀ s t, X (s + t) = X s * X t) {U : Set G} {s t : ℝ}
    {i : ℕ} (hU : ∀ u, |u| ≤ s → X u ∈ U) (ht : |t| * i ≤ s) {j : ℕ} (hj : j ≤ i) :
    X t ^ j ∈ U := by
  rw [pow_eq_of_add hX]
  refine hU _ ?_
  rw [abs_mul, Nat.abs_cast]
  have h1 : (j : ℝ) ≤ i := by exact_mod_cast hj
  have h2 : (j : ℝ) * |t| ≤ i * |t| := mul_le_mul_of_nonneg_right h1 (abs_nonneg t)
  linarith

end KaplanskyLie.StandardSteps

#print axioms KaplanskyLie.StandardSteps.norm_pow_smul_sub_le
#print axioms KaplanskyLie.StandardSteps.pow_mem_of_tendsto_zero
#print axioms KaplanskyLie.StandardSteps.exists_boundary_time
#print axioms KaplanskyLie.StandardSteps.pow_eq_of_add
#print axioms KaplanskyLie.StandardSteps.mem_Q_of_scale
