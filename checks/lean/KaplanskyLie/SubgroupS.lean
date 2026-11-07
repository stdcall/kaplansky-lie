import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The subgroup `S` of lemmas 12, 13 (Chapter II)

Chapter II, § 5, pp. 109-110 (lemmas 12, 13), p. 110 (the last step of lemma 14), § 6, p. 113 (the
end of the proof of theorem 13), § 8 (lemmas 21, 23), § 10, p. 133 (the set `S(Q_i, U)`), p. 135 (the
step `S' ⊆ S` of lemma 43), p. 138 (the Schwarz step of theorem 17).

Notation.  `Δ i` is the book's `Δ_(p(i))` (or `Δ_i` in § 10) and is treated abstractly: `SubAdd Δ U`
lists the properties given by lemma 3, for every `i`.  `S Δ` is the set of `x` for which a sequence
`y_i → x` with `Δ_i(y_i) → 0` exists.  `phiSeq Δ θ i x` is `sup_y (1 - Δ_i(y)) θ(y⁻¹ x)`, the book's
`φ_(p(i))`; `θ` is a continuous function with `0 ≤ θ ≤ 1`, `θ(1) = 1`, `θ(x) < 1` for `x ≠ 1`, vanishing
outside the compact set `U`.

* `Ssubgroup`: `S` is a subgroup (lemma 13, and the remark on p. 133).
* `S_subset`: `S ⊆ U` for closed `U`.
* `S_antitone`: `Δ ≤ Δ'` implies `S Δ' ⊆ S Δ` (lemma 43).
* `S_eq_one`: if `U` contains no subgroup but `{1}`, then `S = {1}`: this is how `φ` becomes
  proper (p. 110).
* `tendsto_phiSeq_iff`: lemma 12: `φ_i(x) → 1` iff `x ∈ S`.
* `lambda_eq_one`: `φ(u y) = λ φ(y)`, `φ(1) = 1`, `φ ≤ 1` give `λ = 1`, `φ(u) = 1` (the end of the
  proof of lemma 14, and p. 138; the equality case of the Cauchy inequality is taken as given).
* `eq_of_shift_eq`: `a f = b f` for a proper `f` implies `a = b` (pp. 113, 117, 118).

Not covered: the convergence `φ_(p(i)) → φ` (Arzela-Ascoli), the integral `ψ`, Cauchy's inequality.
-/

namespace KaplanskyLie.SubgroupS

open Topology Filter Set

variable {G : Type*} [Group G]

/-- The properties of `Δ_i` from lemma 3 used in § 5. -/
structure SubAdd (Δ : ℕ → G → ℝ) (U : Set G) : Prop where
  one : ∀ i, Δ i 1 = 0
  inv : ∀ i x, Δ i x⁻¹ = Δ i x
  mul : ∀ i x y, Δ i (x * y) ≤ Δ i x + Δ i y
  nonneg : ∀ i x, 0 ≤ Δ i x
  off : ∀ i x, x ∉ U → Δ i x = 1

variable [TopologicalSpace G]

/-- The set `S(Q_i, U)` of p. 133, the set of lemma 12. -/
def S (Δ : ℕ → G → ℝ) : Set G :=
  {x | ∃ y : ℕ → G, Tendsto y atTop (𝓝 x) ∧ Tendsto (fun i => Δ i (y i)) atTop (𝓝 0)}

variable [IsTopologicalGroup G]

/-- Lemma 13: `S` is a subgroup. -/
def Ssubgroup {Δ : ℕ → G → ℝ} {U : Set G} (h : SubAdd Δ U) : Subgroup G where
  carrier := S Δ
  one_mem' := ⟨fun _ => 1, tendsto_const_nhds, by simp [h.one]⟩
  mul_mem' := by
    rintro a b ⟨y, hy, hd⟩ ⟨z, hz, he⟩
    refine ⟨fun i => y i * z i, hy.mul hz, ?_⟩
    have hsum : Tendsto (fun i => Δ i (y i) + Δ i (z i)) atTop (𝓝 0) := by
      simpa using hd.add he
    exact squeeze_zero (fun i => h.nonneg i _) (fun i => h.mul i _ _) hsum
  inv_mem' := by
    rintro a ⟨y, hy, hd⟩
    refine ⟨fun i => (y i)⁻¹, hy.inv, ?_⟩
    simpa [h.inv] using hd

omit [IsTopologicalGroup G] in
/-- Lemma 13: `S ⊆ U`, for closed `U`. -/
theorem S_subset {Δ : ℕ → G → ℝ} {U : Set G} (h : SubAdd Δ U) (hU : IsClosed U) : S Δ ⊆ U := by
  rintro x ⟨y, hy, hd⟩
  have hev : ∀ᶠ i in atTop, Δ i (y i) < 1 := hd.eventually (gt_mem_nhds zero_lt_one)
  refine hU.mem_of_tendsto hy (hev.mono fun i hi => ?_)
  by_contra hnot
  rw [h.off i _ hnot] at hi
  exact lt_irrefl _ hi

omit [Group G] [IsTopologicalGroup G] in
/-- The step `S' ⊆ S` of lemma 43. -/
theorem S_antitone {Δ Δ' : ℕ → G → ℝ} (h0 : ∀ i x, 0 ≤ Δ i x) (hle : ∀ i x, Δ i x ≤ Δ' i x) :
    S Δ' ⊆ S Δ := by
  rintro x ⟨y, hy, hd⟩
  exact ⟨y, hy, squeeze_zero (fun i => h0 i _) (fun i => hle i _) hd⟩

/-- `{1}` is the only subgroup contained in `U`. -/
def NoSubgroupIn (U : Set G) : Prop :=
  ∀ T : Subgroup G, (T : Set G) ⊆ U → T = ⊥

/-- P. 110: if `U` contains no subgroup but `{1}`, then `S = {1}`. -/
theorem S_eq_one {Δ : ℕ → G → ℝ} {U : Set G} (h : SubAdd Δ U) (hU : IsClosed U)
    (hS : NoSubgroupIn U) : S Δ = {1} := by
  have hT := hS (Ssubgroup h) (S_subset h hU)
  ext x
  constructor
  · intro hx
    have : x ∈ Ssubgroup h := hx
    rw [hT, Subgroup.mem_bot] at this
    exact this
  · rintro rfl
    exact (Ssubgroup h).one_mem

/-- The book's `φ_(p(i))`. -/
noncomputable def phiSeq (Δ : ℕ → G → ℝ) (θ : G → ℝ) (i : ℕ) (x : G) : ℝ :=
  ⨆ y : G, (1 - Δ i y) * θ (y⁻¹ * x)

omit [IsTopologicalGroup G] in
/-- If `θ(z_i) → 1`, then `z_i → 1`: `θ` is continuous, vanishes outside the compact set `U`, and has a
strict maximum at `1`. -/
theorem tendsto_one_of_theta {θ : G → ℝ} {U : Set G} (hc : Continuous θ) (hU : IsCompact U)
    (hoff : ∀ x, x ∉ U → θ x = 0) (hp : ∀ x, x ≠ 1 → θ x < 1) {z : ℕ → G}
    (hz : Tendsto (fun i => θ (z i)) atTop (𝓝 1)) : Tendsto z atTop (𝓝 1) := by
  rw [tendsto_def]
  intro V hV
  obtain ⟨V', hV's, hV'o, hV'm⟩ := mem_nhds_iff.1 hV
  have hK : IsCompact (U \ V') := hU.diff hV'o
  by_cases hemp : (U \ V').Nonempty
  · obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn hemp hc.continuousOn
    have hw1 : w ≠ 1 := fun e => hw.2 (e ▸ hV'm)
    have hlt : θ w < 1 := hp w hw1
    have hM : (0 : ℝ) < 1 := one_pos
    have hev : ∀ᶠ i in atTop, max (θ w) 0 < θ (z i) :=
      hz.eventually (lt_mem_nhds (max_lt hlt hM))
    refine mem_of_superset hev fun i hi => hV's ?_
    have hi' : max (θ w) 0 < θ (z i) := hi
    by_contra hnot
    by_cases hzU : z i ∈ U
    · have hthis : θ (z i) ≤ θ w := hmax ⟨hzU, hnot⟩
      exact absurd hi' (not_lt.2 (hthis.trans (le_max_left _ _)))
    · rw [hoff _ hzU] at hi'
      exact absurd hi' (not_lt.2 (le_max_right _ _))
  · have hsub : U ⊆ V' := by
      intro x hx
      by_contra hnot
      exact hemp ⟨x, hx, hnot⟩
    have hev : ∀ᶠ i in atTop, (0 : ℝ) < θ (z i) := hz.eventually (lt_mem_nhds one_pos)
    refine mem_of_superset hev fun i hi => hV's (hsub ?_)
    have hi' : (0 : ℝ) < θ (z i) := hi
    by_contra hnot
    rw [hoff _ hnot] at hi'
    exact lt_irrefl _ hi'

/-- Lemma 12. -/
theorem tendsto_phiSeq_iff {Δ : ℕ → G → ℝ} {U : Set G} {θ : G → ℝ} (h : SubAdd Δ U)
    (hd1 : ∀ i x, Δ i x ≤ 1) (hc : Continuous θ) (hUc : IsCompact U) (h0 : ∀ x, 0 ≤ θ x)
    (hle : ∀ x, θ x ≤ 1) (h1 : θ 1 = 1) (hp : ∀ x, x ≠ 1 → θ x < 1)
    (hoff : ∀ x, x ∉ U → θ x = 0) (x : G) :
    Tendsto (fun i => phiSeq Δ θ i x) atTop (𝓝 1) ↔ x ∈ S Δ := by
  have hterm : ∀ i y, (1 - Δ i y) * θ (y⁻¹ * x) ≤ 1 := by
    intro i y
    have a := h.nonneg i y
    have c := hle (y⁻¹ * x)
    have d := h0 (y⁻¹ * x)
    nlinarith [hd1 i y]
  have hb : ∀ i, BddAbove (range fun y => (1 - Δ i y) * θ (y⁻¹ * x)) := fun i =>
    ⟨1, by rintro _ ⟨y, rfl⟩; exact hterm i y⟩
  have hphi1 : ∀ i, phiSeq Δ θ i x ≤ 1 := fun i => ciSup_le fun y => hterm i y
  constructor
  · intro hlim
    have hex : ∀ i : ℕ, ∃ y, phiSeq Δ θ i x - 1 / ((i : ℝ) + 1) < (1 - Δ i y) * θ (y⁻¹ * x) := by
      intro i
      refine exists_lt_of_lt_ciSup ?_
      have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
      unfold phiSeq at *
      linarith
    choose y hy using hex
    have hsmall : Tendsto (fun i : ℕ => phiSeq Δ θ i x - 1 / ((i : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using hlim.sub tendsto_one_div_add_atTop_nhds_zero_nat
    have hd : Tendsto (fun i => Δ i (y i)) atTop (𝓝 0) := by
      have hup : Tendsto (fun i : ℕ => 1 - (phiSeq Δ θ i x - 1 / ((i : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using hsmall.const_sub 1
      refine squeeze_zero (fun i => h.nonneg i _) (fun i => ?_) hup
      have e := hy i
      have f := hle ((y i)⁻¹ * x)
      have g := h0 ((y i)⁻¹ * x)
      have k := h.nonneg i (y i)
      have l := hd1 i (y i)
      nlinarith
    have hθ : Tendsto (fun i => θ ((y i)⁻¹ * x)) atTop (𝓝 1) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hsmall tendsto_const_nhds (fun i => ?_)
        (fun i => hle _)
      have e := hy i
      have g := h0 ((y i)⁻¹ * x)
      have k := h.nonneg i (y i)
      have l := hd1 i (y i)
      simp only at e ⊢
      nlinarith
    have hz := tendsto_one_of_theta hc hUc hoff hp hθ
    refine ⟨y, ?_, hd⟩
    have : Tendsto (fun i => x * ((y i)⁻¹ * x)⁻¹) atTop (𝓝 (x * 1⁻¹)) :=
      tendsto_const_nhds.mul hz.inv
    simpa using this
  · rintro ⟨y, hy, hd⟩
    have hθ : Tendsto (fun i => θ ((y i)⁻¹ * x)) atTop (𝓝 1) := by
      have : Tendsto (fun i => (y i)⁻¹ * x) atTop (𝓝 (x⁻¹ * x)) := hy.inv.mul tendsto_const_nhds
      have h2 : Tendsto (fun i => θ ((y i)⁻¹ * x)) atTop (𝓝 (θ (x⁻¹ * x))) :=
        (hc.tendsto _).comp this
      simpa [h1] using h2
    have hprod : Tendsto (fun i => (1 - Δ i (y i)) * θ ((y i)⁻¹ * x)) atTop (𝓝 1) := by
      simpa using (hd.const_sub 1).mul hθ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hprod tendsto_const_nhds
      (fun i => le_ciSup (hb i) (y i)) hphi1

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The end of the proofs of lemma 14 and theorem 17. -/
theorem lambda_eq_one {φ : G → ℝ} {u : G} {l : ℝ} (h1 : φ 1 = 1) (hle : ∀ x, φ x ≤ 1)
    (hu : ∀ y, φ (u * y) = l * φ y) (hl : 0 ≤ l) : l = 1 ∧ φ u = 1 := by
  have a : φ u = l := by simpa [h1] using hu 1
  have b : (1 : ℝ) = l * φ u⁻¹ := by simpa [h1] using hu u⁻¹
  have c := hle u⁻¹
  have d : l ≤ 1 := a ▸ hle u
  have e : 1 ≤ l := by nlinarith
  have f : l = 1 := le_antisymm d e
  exact ⟨f, a.trans f⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `a f = b f` for a proper `f` implies `a = b`: pp. 113, 117, 118. -/
theorem eq_of_shift_eq {f : G → ℝ} (hp : ∀ x, x ≠ 1 → f x < f 1) {a b : G}
    (h : ∀ x, f (a⁻¹ * x) = f (b⁻¹ * x)) : a = b := by
  by_contra hne
  have hx : b⁻¹ * a ≠ 1 := fun e => hne (by
    have := congrArg (b * ·) e
    simpa using this)
  have := hp _ hx
  rw [← h a] at this
  simp at this

end KaplanskyLie.SubgroupS

#print axioms KaplanskyLie.SubgroupS.Ssubgroup
#print axioms KaplanskyLie.SubgroupS.S_subset
#print axioms KaplanskyLie.SubgroupS.S_antitone
#print axioms KaplanskyLie.SubgroupS.S_eq_one
#print axioms KaplanskyLie.SubgroupS.tendsto_one_of_theta
#print axioms KaplanskyLie.SubgroupS.tendsto_phiSeq_iff
#print axioms KaplanskyLie.SubgroupS.lambda_eq_one
#print axioms KaplanskyLie.SubgroupS.eq_of_shift_eq
