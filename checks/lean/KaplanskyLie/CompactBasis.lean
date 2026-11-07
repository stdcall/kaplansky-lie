import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Lemmas 1, 2 and the construction in theorem 1 of Chapter II

Chapter II, § 2, pp. 91-92.

* `exists_nhds_conj_subset`: lemma 1 (`x⁻¹ V x ⊆ U` for all `x` in a compact `K`), for any
  topological group.
* `exists_subset_of_antitone_compact`: lemma 2 (a decreasing sequence of compact
  neighbourhoods of `z` in a Hausdorff space with intersection `{z}` is a basis at `z`),
  in the form: every open `V ∋ z` contains some `U i`.  Only the compactness of the `U i`
  and the antitonicity are used.
* `W : ℕ → Set G`, the sequence of the proof of theorem 1, is abstracted by the structure
  `Tower`: `1 ∈ W i`, `W i` symmetric, `W (i + 1) W (i + 1) ⊆ W i`, `x⁻¹ W (i + 1) x ⊆ W i` for
  `x ∈ U`.  `Tower.subgroup` is the subgroup `N = ⋂ W i`; `Tower.conj_mem` gives
  `x⁻¹ N x ⊆ N` for `x ∈ U`; `Tower.normal_of_closure_eq_top` shows that `N` is normal if the
  symmetric set `U` generates `G`; `Tower.mem_of_forall_mem_mul`: the images of the `W i` in
  `G/N` have intersection `{1}`, i.e. `⋂ (W i · N) = N`, which is the point where lemma 2 is
  applied in the book.

Not covered: the existence of the `W i` (it is lemma 1 with the local compactness of `G`),
the metrizability theorem quoted on p. 90 (Hewitt-Ross, Abstract Harmonic Analysis I, 2nd ed.,
Theorem (8.3)), theorem 1 itself (Hewitt-Ross, Theorem (8.7) for sigma-compact groups).
-/

namespace KaplanskyLie.CompactBasis

open Topology Filter Set

/-- Lemma 1. -/
theorem exists_nhds_conj_subset {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {U K : Set G} (hU : U ∈ 𝓝 (1 : G)) (hK : IsCompact K) :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ K, ∀ a ∈ V, x⁻¹ * a * x ∈ U := by
  refine hK.induction_on (p := fun s => ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ s, ∀ a ∈ V, x⁻¹ * a * x ∈ U)
    ⟨univ, univ_mem, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨V, hV, h⟩
    exact ⟨V, hV, fun x hx a ha => h x (hst hx) a ha⟩
  · rintro s t ⟨V, hV, h⟩ ⟨V', hV', h'⟩
    refine ⟨V ∩ V', inter_mem hV hV', ?_⟩
    rintro x (hx | hx) a ha
    · exact h x hx a ha.1
    · exact h' x hx a ha.2
  · intro x _
    have hc : Continuous fun p : G × G => p.1⁻¹ * p.2 * p.1 := by fun_prop
    have h1 : (fun p : G × G => p.1⁻¹ * p.2 * p.1) (x, 1) = 1 := by simp
    have hmem : (fun p : G × G => p.1⁻¹ * p.2 * p.1) ⁻¹' U ∈ 𝓝 (x, (1 : G)) :=
      hc.continuousAt (by simpa using hU)
    rw [nhds_prod_eq, mem_prod_iff] at hmem
    obtain ⟨W, hW, V, hV, hsub⟩ := hmem
    refine ⟨W, mem_nhdsWithin_of_mem_nhds hW, V, hV, fun y hy a ha => ?_⟩
    exact hsub (mk_mem_prod hy ha)

/-- Lemma 2. -/
theorem exists_subset_of_antitone_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : ℕ → Set X} {z : X} (ha : Antitone U) (hc : ∀ i, IsCompact (U i))
    (hi : ⋂ i, U i = {z}) {V : Set X} (hV : IsOpen V) (hz : z ∈ V) : ∃ i, U i ⊆ V := by
  by_contra hnot
  simp only [not_exists] at hnot
  have hne : (⋂ i, (U i \ V)).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun i => U i \ V) ?_ ?_ ?_ ?_
    · intro i
      exact sdiff_subset_sdiff_left (ha (Nat.le_succ i))
    · intro i
      exact sdiff_nonempty.2 (hnot i)
    · exact (hc 0).diff hV
    · intro i
      exact (hc i).isClosed.sdiff hV
  obtain ⟨y, hy⟩ := hne
  have hmem : ∀ i, y ∈ U i \ V := fun i => mem_iInter.1 hy i
  have hyz : y ∈ ⋂ i, U i := mem_iInter.2 fun i => (hmem i).1
  rw [hi, mem_singleton_iff] at hyz
  exact (hmem 0).2 (hyz ▸ hz)

/-- The sequence `W_i` of the proof of theorem 1. -/
structure Tower {G : Type*} [Group G] (U : Set G) (W : ℕ → Set G) : Prop where
  one_mem : ∀ i, (1 : G) ∈ W i
  inv_mem : ∀ i, ∀ a ∈ W i, a⁻¹ ∈ W i
  mul_mem : ∀ i, ∀ a ∈ W (i + 1), ∀ b ∈ W (i + 1), a * b ∈ W i
  conj_mem' : ∀ i, ∀ x ∈ U, ∀ a ∈ W (i + 1), x⁻¹ * a * x ∈ W i

namespace Tower

variable {G : Type*} [Group G] {U : Set G} {W : ℕ → Set G}

/-- `N = ⋂ W i`, the subgroup of the proof of theorem 1. -/
def subgroup (h : Tower U W) : Subgroup G where
  carrier := ⋂ i, W i
  one_mem' := mem_iInter.2 h.one_mem
  mul_mem' := fun {a b} ha hb => mem_iInter.2 fun i =>
    h.mul_mem i a (mem_iInter.1 ha _) b (mem_iInter.1 hb _)
  inv_mem' := fun {a} ha => mem_iInter.2 fun i => h.inv_mem i a (mem_iInter.1 ha i)

theorem mem_subgroup (h : Tower U W) {a : G} : a ∈ h.subgroup ↔ ∀ i, a ∈ W i := by
  change a ∈ ⋂ i, W i ↔ _
  exact mem_iInter

/-- `x⁻¹ N x ⊆ N` for `x ∈ U`. -/
theorem conj_mem (h : Tower U W) {x : G} (hx : x ∈ U) {a : G} (ha : a ∈ h.subgroup) :
    x⁻¹ * a * x ∈ h.subgroup :=
  h.mem_subgroup.2 fun i => h.conj_mem' i x hx a (h.mem_subgroup.1 ha _)

/-- If the symmetric set `U` generates `G`, then `N` is a normal subgroup. -/
theorem normal_of_closure_eq_top (h : Tower U W) (hs : ∀ x ∈ U, x⁻¹ ∈ U)
    (hgen : Subgroup.closure U = ⊤) : h.subgroup.Normal := by
  have key : ∀ g : G, (∀ a ∈ h.subgroup, g⁻¹ * a * g ∈ h.subgroup) ∧
      (∀ a ∈ h.subgroup, g * a * g⁻¹ ∈ h.subgroup) := by
    intro g
    have hg : g ∈ Subgroup.closure U := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      refine ⟨fun a ha => h.conj_mem hx ha, fun a ha => ?_⟩
      have := h.conj_mem (hs x hx) ha
      simpa using this
    | one => constructor <;> (intro a ha; simpa using ha)
    | mul x y _ _ ihx ihy =>
      constructor
      · intro a ha
        have := ihy.1 _ (ihx.1 a ha)
        simpa [mul_assoc] using this
      · intro a ha
        have := ihx.2 _ (ihy.2 a ha)
        simpa [mul_assoc] using this
    | inv x _ ihx =>
      constructor
      · intro a ha
        simpa using ihx.2 a ha
      · intro a ha
        simpa using ihx.1 a ha
  exact ⟨fun a ha g => (key g).2 a ha⟩

/-- The images of the `W i` in `G/N` have intersection `{1}`: `⋂ (W i · N) = N`. -/
theorem mem_of_forall_mem_mul (h : Tower U W) {x : G}
    (hx : ∀ i, ∃ a ∈ W i, ∃ n ∈ h.subgroup, x = a * n) : x ∈ h.subgroup := by
  refine h.mem_subgroup.2 fun i => ?_
  obtain ⟨a, ha, n, hn, rfl⟩ := hx (i + 1)
  exact h.mul_mem i a ha n (h.mem_subgroup.1 hn _)

end Tower

end KaplanskyLie.CompactBasis

#print axioms KaplanskyLie.CompactBasis.exists_nhds_conj_subset
#print axioms KaplanskyLie.CompactBasis.exists_subset_of_antitone_compact
#print axioms KaplanskyLie.CompactBasis.Tower.subgroup
#print axioms KaplanskyLie.CompactBasis.Tower.mem_subgroup
#print axioms KaplanskyLie.CompactBasis.Tower.conj_mem
#print axioms KaplanskyLie.CompactBasis.Tower.normal_of_closure_eq_top
#print axioms KaplanskyLie.CompactBasis.Tower.mem_of_forall_mem_mul
