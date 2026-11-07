import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group

/-!
# Steps of § 10 of Chapter II (lemmas 41, 43, theorem 18), § 11, item 1

Chapter II, § 10, pp. 132-139, § 11, p. 139.

Notation.  `NoSubgroupIn W`: `{1}` is the only subgroup contained in `W`.

* `exists_finite_inter_subset`: the compactness step of lemma 41: closed sets of a compact space
  with intersection in an open `V` have a finite subfamily with this property.
* `le_of_subset_preimage`: the step used in lemma 43 and in the proof of theorem 18: if the subset `W`
  of `G/N` contains no subgroup but `{1}`, all subgroups of `G` in the preimage of `W` lie in `N`.
* `exists_nhds_conj_mem`: the «соображения, связанные с конечным покрытием» of p. 139: `a N a⁻¹ ⊆ X` for `a`
  near `1`, if `N` is compact, `X` open, `N ⊆ X`.
* `normal_of_connected`: the end of the printed proof of theorem 18: if `G` is connected, `N` compact,
  `X` open, `N ⊆ X`, and all subgroups in `X` lie in `N`, then `N` is normal.
* `noSubgroup_quotient`, `isNSS_quotient`: the step that the printed proof of theorem 18 leaves out: in
  the same situation, `G/N` is an `NSS`-group.
* `mul_subset_of_le`: the core of § 11, item 1: if `N ⊆ V`, `V V ⊆ U`, then `{x | π(x) ∈ π(V)} = V N ⊆ U`,
  which is why `G → ∏ G/N_i` is a homeomorphism onto its image when the `N_i` are small.

Not covered: Peter-Weyl (lemma 41 uses Hewitt-Ross, Abstract Harmonic Analysis II, Theorem 22.14), theorem
17 (the existence of `X` in the hypotheses above), the closedness of the image in item 1 (Hewitt-Ross,
Abstract Harmonic Analysis I, Theorem (5.11)).
-/

namespace KaplanskyLie.ApproximationSteps

open Topology Filter Set
open scoped Pointwise

/-- `{1}` is the only subgroup contained in `U`. -/
def NoSubgroupIn {G : Type*} [Group G] (U : Set G) : Prop :=
  ∀ S : Subgroup G, (S : Set G) ⊆ U → S = ⊥

/-- The compactness step of lemma 41. -/
theorem exists_finite_inter_subset {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    {S : ι → Set X} (hS : ∀ i, IsClosed (S i)) {V : Set X} (hV : IsOpen V)
    (h : ⋂ i, S i ⊆ V) : ∃ t : Finset ι, ⋂ i ∈ t, S i ⊆ V := by
  have hc : IsCompact Vᶜ := hV.isClosed_compl.isCompact
  have he : Disjoint Vᶜ (⋂ i, S i) := Set.disjoint_left.2 fun x hx hi => hx (h hi)
  obtain ⟨t, ht⟩ := hc.elim_finite_subfamily_closed S hS he
  refine ⟨t, fun x hx => ?_⟩
  by_contra hnot
  exact Set.disjoint_left.1 ht hnot hx

/-- Subgroups in the preimage of a set without subgroups lie in `N`. -/
theorem le_of_subset_preimage {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {W : Set (G ⧸ N)}
    (hW : NoSubgroupIn W) {S : Subgroup G} (hS : ∀ g ∈ S, (g : G ⧸ N) ∈ W) : S ≤ N := by
  have hmap : S.map (QuotientGroup.mk' N) = ⊥ := hW _ (by
    rintro _ ⟨g, hg, rfl⟩
    exact hS g hg)
  intro g hg
  have : (QuotientGroup.mk' N) g ∈ S.map (QuotientGroup.mk' N) := ⟨g, hg, rfl⟩
  rw [hmap, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff g).1 this

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `a N a⁻¹ ⊆ X` for `a` near `1`. -/
theorem exists_nhds_conj_mem {K X : Set G} (hK : IsCompact K) (hX : IsOpen X) (hKX : K ⊆ X) :
    ∃ Y ∈ 𝓝 (1 : G), ∀ a ∈ Y, ∀ n ∈ K, a * n * a⁻¹ ∈ X := by
  refine hK.induction_on (p := fun s => ∃ Y ∈ 𝓝 (1 : G), ∀ a ∈ Y, ∀ n ∈ s, a * n * a⁻¹ ∈ X)
    ⟨univ, univ_mem, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨Y, hY, h⟩
    exact ⟨Y, hY, fun a ha n hn => h a ha n (hst hn)⟩
  · rintro s t ⟨Y, hY, h⟩ ⟨Y', hY', h'⟩
    refine ⟨Y ∩ Y', inter_mem hY hY', ?_⟩
    rintro a ha n (hn | hn)
    · exact h a ha.1 n hn
    · exact h' a ha.2 n hn
  · intro n hn
    have hc : Continuous fun p : G × G => p.1 * p.2 * p.1⁻¹ := by fun_prop
    have hmem : (fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' X ∈ 𝓝 ((1 : G), n) :=
      hc.continuousAt (by simpa using hX.mem_nhds (hKX hn))
    rw [nhds_prod_eq, mem_prod_iff] at hmem
    obtain ⟨Y, hY, W, hW, hsub⟩ := hmem
    refine ⟨W, mem_nhdsWithin_of_mem_nhds hW, Y, hY, fun a ha m hm => ?_⟩
    exact hsub (mk_mem_prod ha hm)

/-- The end of the printed proof of theorem 18. -/
theorem normal_of_connected [ConnectedSpace G] {N : Subgroup G} {X : Set G}
    (hN : IsCompact (N : Set G)) (hX : IsOpen X) (hNX : (N : Set G) ⊆ X)
    (hsub : ∀ S : Subgroup G, (S : Set G) ⊆ X → S ≤ N) : N.Normal := by
  obtain ⟨Y, hY, hconj⟩ := exists_nhds_conj_mem hN hX hNX
  have hstep : ∀ a ∈ Y, ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
    intro a ha n hn
    have hS : ((N.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) ⊆ X := by
      rintro _ ⟨m, hm, rfl⟩
      simpa using hconj a ha m hm
    exact hsub _ hS ⟨n, hn, by simp⟩
  have hY' : Y ∩ Y⁻¹ ∈ 𝓝 (1 : G) := inter_mem hY (by
    have : Continuous fun x : G => x⁻¹ := continuous_inv
    have h2 : (fun x : G => x⁻¹) ⁻¹' Y ∈ 𝓝 (1 : G) :=
      this.continuousAt (by simpa using hY)
    exact h2)
  let H : Subgroup G := Subgroup.normalizer (N : Set G)
  have hnorm : (H : Set G) ∈ 𝓝 (1 : G) := by
    refine mem_of_superset hY' fun a ha => ?_
    refine Subgroup.mem_normalizer_iff.2 fun n => ⟨hstep a ha.1 n, fun h => ?_⟩
    have hinv : a⁻¹ ∈ Y := ha.2
    have := hstep a⁻¹ hinv _ h
    simpa [mul_assoc] using this
  have hopen : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hnorm
  have hclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hopen
  have huniv : (H : Set G) = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨1, H.one_mem⟩
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ H := by
    have : g ∈ (H : Set G) := huniv ▸ mem_univ g
    exact this
  exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The step left out in the printed proof of theorem 18: the image of a small neighbourhood contains
no subgroup but `{1}`. -/
theorem noSubgroup_quotient {N : Subgroup G} [N.Normal] {X X' : Set G}
    (hmul : X' * (N : Set G) ⊆ X) (hsub : ∀ S : Subgroup G, (S : Set G) ⊆ X → S ≤ N) :
    NoSubgroupIn ((fun g : G => (g : G ⧸ N)) '' X') := by
  intro T hT
  have hle : T.comap (QuotientGroup.mk' N) ≤ N := by
    refine hsub _ fun g hg => ?_
    obtain ⟨x, hx, hxg⟩ := hT hg
    have hxg' : (x : G ⧸ N) = (g : G ⧸ N) := hxg
    have hm : x⁻¹ * g ∈ N := QuotientGroup.eq.1 hxg'
    have : g = x * (x⁻¹ * g) := by group
    rw [this]
    exact hmul (mul_mem_mul hx hm)
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).2 (hle hq)

/-- The corrected end of the proof of theorem 18: `G/N` is an `NSS`-group. -/
theorem isNSS_quotient {N : Subgroup G} [N.Normal] {X : Set G} (hN : IsCompact (N : Set G))
    (hX : IsOpen X) (hNX : (N : Set G) ⊆ X)
    (hsub : ∀ S : Subgroup G, (S : Set G) ⊆ X → S ≤ N) :
    ∃ W ∈ 𝓝 (1 : G ⧸ N), NoSubgroupIn W := by
  obtain ⟨V, hV, hVN⟩ := compact_open_separated_mul_left hN hX hNX
  refine ⟨(fun g : G => (g : G ⧸ N)) '' V, ?_, noSubgroup_quotient hVN hsub⟩
  have hopen : IsOpenMap (fun g : G => (g : G ⧸ N)) := QuotientGroup.isOpenMap_coe
  have := hopen.image_mem_nhds hV
  simpa using this

/-- The core of § 11, item 1. -/
theorem mul_subset_of_le {G : Type*} [Group G] {N V U : Set G} (hNV : N ⊆ V) (hVV : V * V ⊆ U) :
    V * N ⊆ U :=
  (mul_subset_mul_left hNV).trans hVV

end KaplanskyLie.ApproximationSteps

#print axioms KaplanskyLie.ApproximationSteps.exists_finite_inter_subset
#print axioms KaplanskyLie.ApproximationSteps.le_of_subset_preimage
#print axioms KaplanskyLie.ApproximationSteps.exists_nhds_conj_mem
#print axioms KaplanskyLie.ApproximationSteps.normal_of_connected
#print axioms KaplanskyLie.ApproximationSteps.noSubgroup_quotient
#print axioms KaplanskyLie.ApproximationSteps.isNSS_quotient
#print axioms KaplanskyLie.ApproximationSteps.mul_subset_of_le
