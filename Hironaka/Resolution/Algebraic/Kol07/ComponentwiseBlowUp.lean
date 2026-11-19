/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Componentwise
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Glue.Product
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.ProductCenter
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The componentwise blow-up lemma

A disjoint union of smooth centers blown up component by component, in a fixed order, gives a
sequence with the same composite as the single blow-up ([Kol07, Remark 33]). The mathematics is
the composition of blow-ups [Sta, Tag 080A] iterated: the blow-up of `X' = B_{D 0} X` along the
inverse image of `D 1` followed by `π_{D 0}` is a blow-up of `X` along `D 0 · D 1`
(`IsBlowUp.comp`), and blow-ups of the same center are canonically isomorphic over `X`
(`IsBlowUp.exists_iso`; the
uniqueness of [Hau14, Remark 4.5]). So the composite of `ofCenters c D` is a blow-up along
`∏ i, D i` for any list of centers; disjointness enters only when the product is identified with
the center `Z` one started from: a regular closed subscheme `V(Z)` is the product of its
irreducible components (`componentFamily`), because its stalks are domains (regular local rings),
so that `Z_x` is prime, has one minimal prime, and one component passes through `x` (the
correspondence of `Hironaka/Resolution/Algebraic/Snc/DictionaryComponents.lean` between minimal
primes of `Z_x` and components through `x`), while the components not through `x` have unit stalk
there.

## Main declarations

* `AlgebraicGeometry.Scheme.BlowUpSequence.isInvertible_comap_stageMap`: an invertible ideal sheaf
  pulls back along every `Π_i` of a blow-up sequence to an invertible one.
* `AlgebraicGeometry.Scheme.BlowUpSequence.center_ofCenters`, `composite_ofCenters_succ`: the
  recursion of `ofCenters` on centers and composites.
* `isBlowUp_composite_ofCenters`, `exists_iso_last_ofCenters` (any list of centers).
* `eq_of_mem_support_componentFamily`, `pairwise_disjoint_support_componentFamily`,
  `prod_componentFamily_eq` (the components of a regular closed subscheme).
* `isBlowUp_composite_componentwiseSeq`, `exists_iso_last_componentwiseSeq`,
  `exceptionalDivisor_comap_eq_prod_componentwiseSeq`,
  `pairwise_disjoint_support_exceptionalAt_componentwiseSeq` (the same for `componentwiseSeq`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme.BlowUpSequence

namespace AlgebraicGeometry.Scheme.BlowUpSequence


variable {X : Scheme.{u}}

/-- An invertible ideal sheaf on `X` pulls back along every partial composite `Π_i : X_i ⟶ X` of a
blow-up sequence to an invertible ideal sheaf (the pull-back of an invertible ideal along a
blow-up is invertible, [Sta, Tag 0809], iterated). -/
theorem isInvertible_comap_stageMap (S : BlowUpSequence X) {K : X.IdealSheafData}
    (hK : K.IsInvertible) (i : Fin (S.length + 1)) : (K.comap (S.stageMap i)).IsInvertible := by
  induction S with
  | nil X =>
    change (K.comap (𝟙 X)).IsInvertible
    rw [comap_id]; exact hK
  | cons X D rest ih =>
    rcases i with ⟨_ | j, hj⟩
    · change (K.comap (𝟙 X)).IsInvertible
      rw [comap_id]; exact hK
    · change (K.comap (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ)).IsInvertible
      rw [comap_comp]
      exact ih (blowUp.isInvertible_comap_of_isInvertible D K hK) _

/-- The composite of `ofCenters (c + 1) D` is the composite of the tail followed by `π_{D 0}`. -/
theorem composite_ofCenters_succ (c : ℕ) (D : Fin (c + 1) → X.IdealSheafData) :
    (ofCenters (c + 1) D).composite =
      (ofCenters c fun i => (D i.succ).comap (D 0).blowUpπ).composite ≫ (D 0).blowUpπ :=
  rfl

/-- The `i`-th center of `ofCenters c D` is the inverse image of `D i` under the composite `Π_i`
of the earlier blow-ups (the preimage `Z_k'` of `Z_k` in the intermediate scheme). -/
theorem center_ofCenters (c : ℕ) (D : Fin c → X.IdealSheafData) (i : Fin (ofCenters c D).length) :
    (ofCenters c D).center i =
      (D (Fin.cast (length_ofCenters c D) i)).comap ((ofCenters c D).stageMap i.castSucc) := by
  induction c generalizing X with
  | zero => exact i.elim0
  | succ c ih =>
    rcases i with ⟨_ | j, hj⟩
    · change D 0 = (D 0).comap (𝟙 X)
      simp
    · change (ofCenters c fun i => (D i.succ).comap (D 0).blowUpπ).center
          ⟨j, Nat.lt_of_succ_lt_succ hj⟩ = _
      rw [ih]
      change ((D _).comap (D 0).blowUpπ).comap _ = (D _).comap
          (_ ≫ (D 0).blowUpπ)
      rw [comap_comp]
      rfl

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The composite of the componentwise sequence is a blow-up along the product -/

/-- The composite of the componentwise sequence of the centers `D 0, …, D (c-1)` is a blow-up of
`X` along their product `∏ i, D i`, in the sense of the universal property [Hau14, Definition 4.4]:
induction on `c` with the composition of blow-ups [Sta, Tag 080A] (`IsBlowUp.comp`) at each step;
the admissibility clause of the step is the invertibility of the exceptional divisor of `π_{D 0}`
pulled back along the composite of the later blow-ups (`isInvertible_comap_stageMap`). -/
theorem isBlowUp_composite_ofCenters (c : ℕ) (D : Fin c → X.IdealSheafData) :
    IsBlowUp (∏ i, D i) (ofCenters c D).composite := by
  induction c generalizing X with
  | zero =>
    change IsBlowUp (∏ i : Fin 0, D i) (𝟙 X)
    rw [Fin.prod_univ_zero, one_eq_top]
    refine ⟨?_, fun f _ => ⟨f, Category.comp_id f, fun g hg => (Category.comp_id g).symm.trans hg⟩⟩
    rw [comap_top]
    exact isInvertible_top
  | succ c ih =>
    rw [composite_ofCenters_succ, Fin.prod_univ_succ]
    have hrest := ih (fun i => (D i.succ).comap (D 0).blowUpπ)
    rw [← comap_finset_prod] at hrest
    refine (blowUp.isBlowUp (D 0)).comp hrest ?_
    have h := isInvertible_comap_stageMap (ofCenters c fun i => (D i.succ).comap
        (D 0).blowUpπ)
      (blowUp.isInvertible_comap_π (D 0)) (Fin.last _)
    rw [← comap_comp] at h
    exact h

/-- The end result of the componentwise sequence is isomorphic over `X` to the blow-up along the
product, by a unique morphism over `X` (`IsBlowUp.exists_iso`; [Hau14, Remark 4.5]). -/
theorem exists_iso_last_ofCenters (c : ℕ) (D : Fin c → X.IdealSheafData) :
    ∃ e : (ofCenters c D).last ≅ (∏ i, D i).blowUp,
      e.hom ≫ (∏ i, D i).blowUpπ = (ofCenters c D).composite ∧
        ∀ ψ : (ofCenters c D).last ⟶ (∏ i, D i).blowUp,
          ψ ≫ (∏ i, D i).blowUpπ = (ofCenters c D).composite → ψ = e.hom :=
  (isBlowUp_composite_ofCenters c D).exists_iso (blowUp.isBlowUp _)

/-- The `k`-th exceptional divisor of the componentwise sequence, pulled up to the end result along
Kollár's `Π_{c,k+1}` [Kol07, Definition 29], is the inverse image of the `k`-th center under the
composite `Π_c`. -/
theorem exceptionalAt_comap_stageMapBetween_last (c : ℕ) (D : Fin c → X.IdealSheafData)
    (i : Fin (ofCenters c D).length) :
    ((ofCenters c D).exceptionalAt i).comap
        ((ofCenters c D).stageMapBetween (Fin.last _) i.succ (Fin.le_last _)) =
      (D (Fin.cast (length_ofCenters c D) i)).comap (ofCenters c D).composite := by
  change (((ofCenters c D).center i).comap ((ofCenters c D).step i)).comap _ = _
  rw [← comap_comp, ← stageMapBetween_succ_castSucc, stageMapBetween_comp, center_ofCenters,
    ← comap_comp, stageMapBetween_comp_stageMap]
  rfl

/-! ### The irreducible components of a regular closed subscheme -/

section Components

variable [NoetherianSpace X] (Z : X.IdealSheafData)

omit [NoetherianSpace X] in
/-- At a point of a regular closed subscheme `V(Z)` the stalk ideal `Z_x` is prime:
`𝒪_{X,x}/Z_x ≅ 𝒪_{V(Z),z}` (`stalkQuotientEquiv`) is a regular local ring, hence a domain. -/
theorem isPrime_stalkIdeal_of_isRegular (hZ : IsRegular Z.subscheme) {x : X}
    (hx : x ∈ Z.support) : (Z.stalkIdeal x).IsPrime := by
  obtain ⟨z, rfl⟩ := Z.exists_subschemeι_eq hx
  have hreg : IsRegularLocalRing (Z.subscheme.presheaf.stalk z) := hZ.isRegularAt z
  have : IsDomain (X.presheaf.stalk (Z.subschemeι z) ⧸ Z.stalkIdeal (Z.subschemeι z)) :=
    Function.Injective.isDomain (Z.stalkQuotientEquiv z) (Z.stalkQuotientEquiv z).injective
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

omit [NoetherianSpace X] in
/-- A point `x` of a regular closed subscheme `V(Z)` lies on exactly one irreducible component: two
generic points of `V(Z)` specializing to `x` both give the unique minimal prime `Z_x` of the prime
`Z_x` (`stalkIdeal_vanishingIdeal_mem_minimalPrimes`,
`eq_of_stalkIdeal_vanishingIdeal_closure_eq`). -/
theorem eq_of_specializes_of_isRegular (hZ : IsRegular Z.subscheme) {η η' x : X}
    (hη : η ∈ Z.support.genericPoints) (hη' : η' ∈ Z.support.genericPoints) (hηx : η ⤳ x)
    (hη'x : η' ⤳ x) : η = η' := by
  have hx : x ∈ Z.support := hηx.mem_closed Z.support.isClosed hη.1
  have hP := stalkIdeal_vanishingIdeal_mem_minimalPrimes Z hη hηx
  have hP' := stalkIdeal_vanishingIdeal_mem_minimalPrimes Z hη' hη'x
  have hprime := isPrime_stalkIdeal_of_isRegular Z hZ hx
  rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hP hP'
  exact eq_of_stalkIdeal_vanishingIdeal_closure_eq hηx hη'x (hP.trans hP'.symm)

/-- The support of a member of the component family is the closure of its generic point. -/
theorem mem_support_componentFamily_iff (η : Z.componentFamily.ι) (x : X) :
    x ∈ (Z.componentFamily.component η).support ↔ η.1 ⤳ x := by
  change x ∈ (vanishingIdeal (Closeds.closure {η.1})).support ↔ _
  rw [← SetLike.mem_coe, coe_support_vanishingIdeal, SetLike.mem_coe, Closeds.mem_closure,
    specializes_iff_mem_closure]

/-- Two members of the component family of a regular closed subscheme with a common point
coincide. -/
theorem eq_of_mem_support_componentFamily (hZ : IsRegular Z.subscheme)
    {i j : Z.componentFamily.ι} {x : X} (hi : x ∈ (Z.componentFamily.component i).support)
    (hj : x ∈ (Z.componentFamily.component j).support) : i = j := by
  rw [mem_support_componentFamily_iff] at hi hj
  exact Subtype.ext (eq_of_specializes_of_isRegular Z hZ i.2 j.2 hi hj)

/-- The irreducible components of a regular closed subscheme `V(Z)` are pairwise disjoint. -/
theorem pairwise_disjoint_support_componentFamily (hZ : IsRegular Z.subscheme) :
    Pairwise fun i j => Disjoint (Z.componentFamily.component i).support
      (Z.componentFamily.component j).support := by
  intro i j hij
  rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot,
    Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hi, hj⟩
  exact hij (eq_of_mem_support_componentFamily Z hZ hi hj)

/-- A regular closed subscheme is the product of its irreducible components (`Z = ∐ Z_k`), stalk
by stalk: at `x ∈ V(Z)` the unique component through `x` has stalk `Z_x` (the unique minimal prime
of the prime `Z_x`) and the others have unit stalk; off `V(Z)` every stalk is the unit ideal. -/
theorem prod_componentFamily_eq (hZ : IsRegular Z.subscheme) :
    ∏ i, Z.componentFamily.component i = Z := by
  classical
  refine ext_stalkIdeal fun x => ?_
  rw [stalkIdeal_finset_prod]
  by_cases hx : x ∈ Z.support
  · have hprime := isPrime_stalkIdeal_of_isRegular Z hZ hx
    obtain ⟨η, hη, hηx, hP⟩ := exists_mem_genericPoints_of_mem_minimalPrimes Z
      (P := Z.stalkIdeal x)
      (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
    rw [Finset.prod_eq_single ⟨η, hη⟩]
    · exact hP
    · intro j _ hj
      rw [Ideal.one_eq_top]
      refine stalkIdeal_eq_top_of_notMem_support _ fun hxj => hj ?_
      refine eq_of_mem_support_componentFamily Z hZ hxj ?_
      exact (mem_support_componentFamily_iff Z ⟨η, hη⟩ x).mpr hηx
    · exact fun h => (h (Finset.mem_univ _)).elim
  · rw [stalkIdeal_eq_top_of_notMem_support Z hx, ← Ideal.one_eq_top]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Ideal.one_eq_top]
    refine stalkIdeal_eq_top_of_notMem_support _ fun hxj => hx ?_
    rw [mem_support_componentFamily_iff] at hxj
    exact hxj.mem_closed Z.support.isClosed j.2.1

/-- At a point of an irreducible component of a regular closed subscheme `V(Z)`, the stalk of the
component is the stalk of `Z`, the unique minimal prime of the prime `Z_x`. -/
theorem stalkIdeal_componentFamily_eq (hZ : IsRegular Z.subscheme) (η : Z.componentFamily.ι)
    {x : X} (hx : x ∈ (Z.componentFamily.component η).support) :
    (Z.componentFamily.component η).stalkIdeal x = Z.stalkIdeal x := by
  have hηx : η.1 ⤳ x := (mem_support_componentFamily_iff Z η x).mp hx
  have hxZ : x ∈ Z.support := hηx.mem_closed Z.support.isClosed η.2.1
  have hprime := isPrime_stalkIdeal_of_isRegular Z hZ hxZ
  obtain ⟨η', hη', hη'x, hP⟩ := exists_mem_genericPoints_of_mem_minimalPrimes Z
    (P := Z.stalkIdeal x)
    (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
  have heq : (⟨η', hη'⟩ : Z.componentFamily.ι) = η :=
    eq_of_mem_support_componentFamily Z hZ
      ((mem_support_componentFamily_iff Z ⟨η', hη'⟩ x).mpr hη'x) hx
  rw [← heq]
  exact hP

/-- The closed subscheme of a member of the component family is an irreducible space: its
underlying space is the closure of the generic point. -/
theorem irreducibleSpace_subscheme_componentFamily (η : Z.componentFamily.ι) :
    IrreducibleSpace (Z.componentFamily.component η).subscheme := by
  have hemb : Topology.IsEmbedding (Z.componentFamily.component η).subschemeι.base :=
    (Z.componentFamily.component η).subschemeι.isClosedEmbedding.isEmbedding
  rw [Homeomorph.irreducibleSpace_iff hemb.toHomeomorph, ← isIrreducible_iff_irreducibleSpace,
    range_subschemeι]
  change IsIrreducible ((vanishingIdeal (Closeds.closure {η.1})).support : Set X)
  rw [coe_support_vanishingIdeal]
  exact isIrreducible_singleton.closure

/-- The irreducible components of a regular closed subscheme are regular: their stalks are the
stalks of `V(Z)` (`stalkIdeal_componentFamily_eq`). -/
theorem isRegular_subscheme_componentFamily (hZ : IsRegular Z.subscheme)
    (η : Z.componentFamily.ι) : IsRegular (Z.componentFamily.component η).subscheme := by
  refine isRegular_subscheme_of_isRegularLocalRing_quotient _ fun w hw => ?_
  rw [stalkIdeal_componentFamily_eq Z hZ η hw]
  have hwZ : w ∈ Z.support :=
    ((mem_support_componentFamily_iff Z η w).mp hw).mem_closed Z.support.isClosed η.2.1
  obtain ⟨z, rfl⟩ := Z.exists_subschemeι_eq hwZ
  have : IsRegularLocalRing (Z.subscheme.presheaf.stalk z) := hZ.isRegularAt z
  exact IsRegularLocalRing.of_ringEquiv (Z.stalkQuotientEquiv z).symm

/-! ### The componentwise sequence of a regular center -/

/-- The composite of the componentwise sequence of a regular center `Z` is a blow-up of `X` along
`Z`: the blow-up `π_Z` factors as `π_{Z_1} ∘ π_{Z_2'} ∘ ⋯ ∘ π_{Z_c'}`. -/
theorem isBlowUp_composite_componentwiseSeq (hZ : IsRegular Z.subscheme) :
    IsBlowUp Z Z.componentwiseSeq.composite := by
  have h := isBlowUp_composite_ofCenters _ Z.componentFamily.nth
  rwa [Scheme.DivisorFamily.prod_orderedComponent, prod_componentFamily_eq Z hZ] at h

/-- The end result of the componentwise sequence of a regular center is canonically isomorphic to
`B_Z X`, over `X`. -/
theorem exists_iso_last_componentwiseSeq (hZ : IsRegular Z.subscheme) :
    ∃ e : Z.componentwiseSeq.last ≅ Z.blowUp,
      e.hom ≫ Z.blowUpπ = Z.componentwiseSeq.composite :=
  let ⟨e, he, _⟩ := (isBlowUp_composite_componentwiseSeq Z hZ).exists_iso (blowUp.isBlowUp Z)
  ⟨e, he⟩

/-- The exceptional divisor of `π_Z` is the disjoint union of the exceptional divisors of the
componentwise blow-ups, the union: under any morphism `e` over `X` from the end result of the
componentwise sequence to `B_Z X`, the exceptional divisor of `π_Z` pulls back to the product of
the exceptional divisors of the componentwise blow-ups pulled up to the end result. -/
theorem exceptionalDivisor_comap_eq_prod_componentwiseSeq (hZ : IsRegular Z.subscheme)
    (e : Z.componentwiseSeq.last ⟶ Z.blowUp)
    (he : e ≫ Z.blowUpπ = Z.componentwiseSeq.composite) :
    Z.exceptionalDivisor.comap e =
      ∏ i : Fin Z.componentwiseSeq.length,
        (Z.componentwiseSeq.exceptionalAt i).comap
          (Z.componentwiseSeq.stageMapBetween (Fin.last _) i.succ (Fin.le_last _)) := by
  have hlen : Z.componentwiseSeq.length = Fintype.card Z.componentFamily.ι :=
    length_ofCenters _ Z.componentFamily.nth
  have key : ∀ i : Fin Z.componentwiseSeq.length,
      (Z.componentwiseSeq.exceptionalAt i).comap
          (Z.componentwiseSeq.stageMapBetween (Fin.last _) i.succ (Fin.le_last _)) =
        (Z.componentFamily.nth (Fin.cast hlen i)).comap
          Z.componentwiseSeq.composite :=
    fun i => exceptionalAt_comap_stageMapBetween_last _ _ i
  have hZ' : ∏ i : Fin Z.componentwiseSeq.length,
      Z.componentFamily.nth (Fin.cast hlen i) = Z :=
    (Fintype.prod_equiv (finCongr hlen) _ _ fun _ => rfl).trans
      ((Scheme.DivisorFamily.prod_orderedComponent _).trans
          (prod_componentFamily_eq Z hZ))
  change (Z.comap Z.blowUpπ).comap e = _
  rw [← comap_comp, he, Finset.prod_congr rfl fun i _ => key i]
  calc Z.comap Z.componentwiseSeq.composite
      = (∏ i : Fin Z.componentwiseSeq.length,
          Z.componentFamily.nth (Fin.cast hlen i)).comap
            Z.componentwiseSeq.composite := by rw [hZ']
    _ = _ := comap_finset_prod _ _ _

/-- The exceptional divisor of `π_Z` is the disjoint union of the exceptional divisors of the
componentwise blow-ups, the disjointness: the exceptional divisors of the componentwise blow-ups,
pulled up to the end result, have pairwise disjoint supports, as they lie over the pairwise
disjoint components. -/
theorem pairwise_disjoint_support_exceptionalAt_componentwiseSeq (hZ : IsRegular Z.subscheme) :
    Pairwise fun i j : Fin Z.componentwiseSeq.length =>
      Disjoint
        ((Z.componentwiseSeq.exceptionalAt i).comap
          (Z.componentwiseSeq.stageMapBetween (Fin.last _) i.succ (Fin.le_last _))).support
        ((Z.componentwiseSeq.exceptionalAt j).comap
          (Z.componentwiseSeq.stageMapBetween (Fin.last _) j.succ (Fin.le_last _))).support := by
  intro i j hij
  have hlen : Z.componentwiseSeq.length = Fintype.card Z.componentFamily.ι :=
    length_ofCenters _ Z.componentFamily.nth
  have key : ∀ i : Fin Z.componentwiseSeq.length,
      (Z.componentwiseSeq.exceptionalAt i).comap
          (Z.componentwiseSeq.stageMapBetween (Fin.last _) i.succ (Fin.le_last _)) =
        (Z.componentFamily.component (monoEquivOfFin _ rfl (Fin.cast hlen i))).comap
          Z.componentwiseSeq.composite :=
    fun i => exceptionalAt_comap_stageMapBetween_last _ _ i
  have hd : Disjoint
      (Z.componentFamily.component (monoEquivOfFin _ rfl (Fin.cast hlen i))).support
      (Z.componentFamily.component (monoEquivOfFin _ rfl (Fin.cast hlen j))).support :=
    pairwise_disjoint_support_componentFamily Z hZ fun h =>
      hij ((finCongr hlen).injective ((monoEquivOfFin _ rfl).injective h))
  rw [key i, key j]
  rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot,
    Set.eq_empty_iff_forall_notMem] at hd ⊢
  rintro y ⟨hy₁, hy₂⟩
  exact hd _ ⟨(mem_support_comap_iff_apply _ Z.componentwiseSeq.composite y).mp hy₁,
    (mem_support_comap_iff_apply _ Z.componentwiseSeq.composite y).mp hy₂⟩

end Components

end Hironaka.Sequence
