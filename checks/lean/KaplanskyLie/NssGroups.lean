import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Constructions
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# `NSS`-groups: the exercises of § 1 of Chapter II

Chapter II, § 1, pp. 88-90.  `NoSubgroupIn U` says that `{1}` is the only subgroup
contained in `U`; `IsNSS G` says that a neighbourhood of `1` has this property.  Groups
are topological groups, not necessarily Hausdorff or locally compact: the book
assumes neither in § 1.

* `eq_one_of_forall_zpow_mem`, `eq_one_of_forall_pow_mem`: an element all of whose powers
  lie in `U` (symmetric, for the second) is `1`.  This is the step used in the proofs of
  theorems 3, 4, lemma 15 and lemma 30.
* `exists_pow_not_mem`: the first power outside `U` exists for `x ≠ 1`.
* `discreteTopology_of_pow_eq_one`: exercise 1 (bounded orders imply discreteness).
* `isNSS_of_ker_of_range`: exercise 2 for a continuous homomorphism `f` (with `H = ker f`,
  `G/H` the target): if `ker f` and the target are `NSS`, so is `G`.
* `isNSS_quotient_extension`: exercise 2 as printed, for a normal subgroup `H`.
* `isNSS_pi`: exercise 3, `isNSS_prod`: the case of two factors.
* `not_isNSS_pi`: exercise 4.
* `isNSS_of_injective`: exercise 5; `isNSS_subgroup`: subgroups of `NSS`-groups.
* `isNSS_quotient_inf`: § 11, item 3 (a): if `G/N` and `G/H` are `NSS`, so is `G/(N ⊓ H)`.

Not covered: the examples 1-6 of § 1 (exercise 1's counterexample and the examples are
tested in `checks/sage/chapter-2a.py`), the closing question of § 1, and all locally compact
theory.
-/

namespace KaplanskyLie.NssGroups

open Topology Filter Set

/-- `{1}` is the only subgroup contained in `U`. -/
def NoSubgroupIn {G : Type*} [Group G] (U : Set G) : Prop :=
  ∀ S : Subgroup G, (S : Set G) ⊆ U → S = ⊥

/-- The book's `NSS`-group. -/
def IsNSS (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), NoSubgroupIn U

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

theorem exists_pow_not_mem {G : Type*} [Group G] {U : Set G}
    (hU : NoSubgroupIn U) (hs : ∀ y ∈ U, y⁻¹ ∈ U) {x : G} (hx : x ≠ 1) :
    ∃ n : ℕ, x ^ n ∉ U := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hx (eq_one_of_forall_pow_mem hU hs h)

/-- Exercise 1: an `NSS`-group of bounded orders is discrete. -/
theorem discreteTopology_of_pow_eq_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (h : IsNSS G) {N : ℕ} (hN : 0 < N) (hx : ∀ x : G, x ^ N = 1) :
    DiscreteTopology G := by
  obtain ⟨U, hU, hS⟩ := h
  have hV : (⋂ k ∈ Finset.range N, (fun x : G => x ^ k) ⁻¹' U) ∈ 𝓝 (1 : G) := by
    refine (Filter.biInter_finset_mem _).2 fun k _ => ?_
    have hc : ContinuousAt (fun x : G => x ^ k) 1 := (continuous_pow k).continuousAt
    exact hc (by simpa using hU)
  have hsub : (⋂ k ∈ Finset.range N, (fun x : G => x ^ k) ⁻¹' U) ⊆ {1} := by
    intro x hxV
    simp only [mem_iInter, Finset.mem_range, mem_preimage] at hxV
    have : x = 1 := by
      refine eq_one_of_forall_zpow_mem hS fun k => ?_
      have hN' : (0 : ℤ) < N := by exact_mod_cast hN
      have hm : 0 ≤ k % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
      have hl : k % (N : ℤ) < N := Int.emod_lt_of_pos _ hN'
      obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hm
      have hrN : r < N := by omega
      have hk : x ^ k = x ^ r := by
        conv_lhs => rw [← Int.emod_add_mul_ediv k N, hr]
        rw [zpow_add, zpow_mul, zpow_natCast, zpow_natCast, hx, one_zpow, mul_one]
      rw [hk]
      exact hxV r hrN
    simpa using this
  have hone : ({1} : Set G) ∈ 𝓝 (1 : G) := mem_of_superset hV hsub
  have hopen : IsOpen ({1} : Set G) := by
    rw [isOpen_iff_mem_nhds]
    intro a ha
    rw [mem_singleton_iff] at ha
    rw [ha]
    exact hone
  exact discreteTopology_of_isOpen_singleton_one hopen

/-- Exercise 2 for a continuous homomorphism: `H = ker f`, `G/H` the target. -/
theorem isNSS_of_ker_of_range {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q]
    [TopologicalSpace Q] (f : G →* Q) (hf : Continuous f) (hQ : IsNSS Q) (hH : IsNSS f.ker) :
    IsNSS G := by
  obtain ⟨W, hW, hWS⟩ := hQ
  obtain ⟨U', hU', hUS⟩ := hH
  rw [mem_nhds_subtype] at hU'
  obtain ⟨U, hU, hUU'⟩ := hU'
  refine ⟨U ∩ f ⁻¹' W, inter_mem hU (hf.continuousAt (by simpa using hW)), ?_⟩
  intro S hS
  have hmap : S.map f = ⊥ := hWS _ (by
    rintro _ ⟨x, hx, rfl⟩
    exact (hS hx).2)
  have hker : S ≤ f.ker := (Subgroup.map_eq_bot_iff _).1 hmap
  have hof : S.subgroupOf f.ker = ⊥ := hUS _ (by
    intro x hx
    exact hUU' (hS (Subgroup.mem_subgroupOf.1 hx)).1)
  have hd := (Subgroup.subgroupOf_eq_bot).1 hof
  have he := hd.eq_bot
  rwa [inf_eq_left.2 hker] at he

/-- Exercise 2 as printed: `H` normal, `H` and `G/H` are `NSS`. -/
theorem isNSS_quotient_extension {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) [H.Normal] (hH : IsNSS H) (hQ : IsNSS (G ⧸ H)) :
    IsNSS G := by
  refine isNSS_of_ker_of_range (QuotientGroup.mk' H) QuotientGroup.continuous_mk hQ ?_
  have : (QuotientGroup.mk' H).ker = H := QuotientGroup.ker_mk' H
  rw [this]
  exact hH

/-- Exercise 3: a finite product of `NSS`-groups is an `NSS`-group. -/
theorem isNSS_pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] (h : ∀ i, IsNSS (G i)) : IsNSS (∀ i, G i) := by
  choose U hU hS using h
  refine ⟨Set.pi univ U, set_pi_mem_nhds finite_univ fun i _ => hU i, ?_⟩
  intro S hSU
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  funext i
  have hmap : S.map (Pi.evalMonoidHom G i) = ⊥ := hS i _ (by
    rintro _ ⟨y, hy, rfl⟩
    exact hSU hy i (mem_univ i))
  have : (Pi.evalMonoidHom G i) x ∈ S.map (Pi.evalMonoidHom G i) := ⟨x, hx, rfl⟩
  rw [hmap, Subgroup.mem_bot] at this
  exact this

/-- Exercise 3 for two factors. -/
theorem isNSS_prod {A B : Type*} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
    (hA : IsNSS A) (hB : IsNSS B) : IsNSS (A × B) := by
  obtain ⟨U, hU, hUS⟩ := hA
  obtain ⟨V, hV, hVS⟩ := hB
  refine ⟨U ×ˢ V, prod_mem_nhds hU hV, ?_⟩
  intro S hS
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : S.map (MonoidHom.fst A B) = ⊥ := hUS _ (by
    rintro _ ⟨y, hy, rfl⟩
    exact (hS hy).1)
  have h2 : S.map (MonoidHom.snd A B) = ⊥ := hVS _ (by
    rintro _ ⟨y, hy, rfl⟩
    exact (hS hy).2)
  have a1 : (MonoidHom.fst A B) x ∈ S.map (MonoidHom.fst A B) := ⟨x, hx, rfl⟩
  have a2 : (MonoidHom.snd A B) x ∈ S.map (MonoidHom.snd A B) := ⟨x, hx, rfl⟩
  rw [h1, Subgroup.mem_bot] at a1
  rw [h2, Subgroup.mem_bot] at a2
  exact Prod.ext a1 a2

/-- Exercise 4: an infinite product of nontrivial groups is not an `NSS`-group. -/
theorem not_isNSS_pi {ι : Type*} [Infinite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, Nontrivial (G i)] : ¬ IsNSS (∀ i, G i) := by
  classical
  rintro ⟨U, hU, hS⟩
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  let T : Subgroup (∀ i, G i) :=
    { carrier := {x | ∀ i ∈ I, x i = 1}
      one_mem' := fun _ _ => rfl
      mul_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
      inv_mem' := fun {a} ha i hi => by simp [ha i hi] }
  have hT : T = ⊥ := hS T (by
    intro x hx
    apply hsub
    intro i hi
    rw [hx i hi]
    exact mem_of_mem_nhds (ht i))
  obtain ⟨j, hj⟩ := hI.exists_notMem
  obtain ⟨a, ha⟩ := exists_ne (1 : G j)
  have hmem : Function.update (1 : ∀ i, G i) j a ∈ T := by
    intro i hi
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [Function.update_of_ne hne]
  rw [hT, Subgroup.mem_bot] at hmem
  have := congrFun hmem j
  simp at this
  exact ha this

/-- Exercise 5: a continuous injective homomorphism into an `NSS`-group. -/
theorem isNSS_of_injective {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (f : G →* H) (hf : Continuous f) (hi : Function.Injective f)
    (hH : IsNSS H) : IsNSS G := by
  obtain ⟨U, hU, hS⟩ := hH
  refine ⟨f ⁻¹' U, hf.continuousAt (by simpa using hU), ?_⟩
  intro S hSU
  have hmap : S.map f = ⊥ := hS _ (by
    rintro _ ⟨x, hx, rfl⟩
    exact hSU hx)
  exact (Subgroup.map_eq_bot_iff_of_injective _ hi).1 hmap

/-- A subgroup of an `NSS`-group is an `NSS`-group (the remark in exercise 5). -/
theorem isNSS_subgroup {G : Type*} [Group G] [TopologicalSpace G] (hG : IsNSS G)
    (S : Subgroup G) : IsNSS S :=
  isNSS_of_injective S.subtype continuous_subtype_val Subtype.val_injective hG

/-- § 11, item 3 (a): `G/(N ⊓ H)` maps continuously and injectively into `G/N × G/H`,
hence it is an `NSS`-group. -/
theorem isNSS_quotient_inf {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N H : Subgroup G) [N.Normal] [H.Normal] (hN : IsNSS (G ⧸ N)) (hH : IsNSS (G ⧸ H)) :
    IsNSS (G ⧸ (N ⊓ H)) := by
  let g : G →* (G ⧸ N) × (G ⧸ H) := (QuotientGroup.mk' N).prod (QuotientGroup.mk' H)
  have hker : N ⊓ H ≤ g.ker := by
    intro x hx
    have h1 : (x : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff x).2 hx.1
    have h2 : (x : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff x).2 hx.2
    rw [MonoidHom.mem_ker]
    exact Prod.ext h1 h2
  let f : G ⧸ (N ⊓ H) →* (G ⧸ N) × (G ⧸ H) := QuotientGroup.lift (N ⊓ H) g hker
  have hg : Continuous g :=
    (QuotientGroup.continuous_mk (N := N)).prodMk (QuotientGroup.continuous_mk (N := H))
  have hf : Continuous f := by
    refine continuous_quot_lift _ ?_
    exact hg
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have h' : g x = 1 := hy
    have h1 : (x : G ⧸ N) = 1 := congrArg Prod.fst h'
    have h2 : (x : G ⧸ H) = 1 := congrArg Prod.snd h'
    exact (QuotientGroup.eq_one_iff x).2
      ⟨(QuotientGroup.eq_one_iff x).1 h1, (QuotientGroup.eq_one_iff x).1 h2⟩
  exact isNSS_of_injective f hf hinj (isNSS_prod hN hH)

end KaplanskyLie.NssGroups

#print axioms KaplanskyLie.NssGroups.eq_one_of_forall_zpow_mem
#print axioms KaplanskyLie.NssGroups.eq_one_of_forall_pow_mem
#print axioms KaplanskyLie.NssGroups.exists_pow_not_mem
#print axioms KaplanskyLie.NssGroups.discreteTopology_of_pow_eq_one
#print axioms KaplanskyLie.NssGroups.isNSS_of_ker_of_range
#print axioms KaplanskyLie.NssGroups.isNSS_quotient_extension
#print axioms KaplanskyLie.NssGroups.isNSS_pi
#print axioms KaplanskyLie.NssGroups.isNSS_prod
#print axioms KaplanskyLie.NssGroups.not_isNSS_pi
#print axioms KaplanskyLie.NssGroups.isNSS_of_injective
#print axioms KaplanskyLie.NssGroups.isNSS_subgroup
#print axioms KaplanskyLie.NssGroups.isNSS_quotient_inf
