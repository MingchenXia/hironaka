/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.ValCurves.ModificationsFinite
import DeJongAlterations.StableModification.ValuationRing.FibreDimension
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Bezout
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Closures of algebraic points over a valuation ring with separably closed residue fields

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (T:3115–3118): after shrinking `C` so that `x` is the only closed point of the
modification locus `V`, "since `V` is closed in `C̄`, we can extend `f` trivially". This needs
that the closures in the compactification `C̄` of the (finitely many) generizations of `x` in `V`
do not meet the closed fibre outside `x` (ERRATA T11). This file proves it
(`specializes_of_specializes_of_isAlgebraicAt`, blueprint `lem:sm-bd-closure-local`): over a
valuation ring `V` all of whose residue fields `Frac(V/𝔭)` are separably closed (Temkin's
valuation rings of `K^s`), the closure of a point `t` of a proper `V`-scheme which is algebraic
over its image is the spectrum of a *local* ring finite over `V`, so all its points are
generizations of its unique closed point.

## Main results

* `isLocalRing_of_forall_pow_mem`: an integral extension `B` of a local ring `A` in which every
  element has a power coming from `A` is local.
* `exists_pow_mem_of_isSepClosed`: if `B` is a domain integral over a valuation ring `A` whose
  fraction field is separably closed, every element of `B` has a power in `A`
  (`Frac B / Frac A` is purely inseparable and `A` is integrally closed).
* `specializes_of_specializes_of_isAlgebraicAt`: for `g : X → Spec V` proper and `t ⤳ x` with
  `x` closed and `κ(t)` algebraic over the base, every specialization of `t` is a generization of
  `x`.
* `isClosed_of_forall_specializes`: a finite subset `T` of an open `U ∋ x`, closed in `U`, of such
  generizations of `x` is closed in `X` (blueprint `lem:sm-bd-closed-locus`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.BlowDown

universe u

section Algebra

/-- **Integral extensions with powers in the base are local**: if `B ≠ 0` is integral over the
local ring `A` and every `b ∈ B` has a positive power in the image of `A`, then `B` is local. -/
theorem isLocalRing_of_forall_pow_mem {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [Nontrivial B] [Algebra A B] [Algebra.IsIntegral A B]
    (h : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ (algebraMap A B).range) : IsLocalRing B := by
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  have hc : ∀ N : Ideal B, N.IsMaximal →
      N.comap (algebraMap A B) = IsLocalRing.maximalIdeal A := fun N hN =>
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N)
  have key : ∀ N N' : Ideal B, N.IsMaximal → N'.IsMaximal → N ≤ N' := by
    intro N N' hN hN' b hb
    obtain ⟨n, hn, a, ha⟩ := h b
    have hmem : a ∈ N.comap (algebraMap A B) := by
      rw [Ideal.mem_comap, ha]
      exact Ideal.pow_mem_of_mem N hb n hn
    rw [hc N hN, ← hc N' hN', Ideal.mem_comap, ha] at hmem
    exact hN'.isPrime.mem_of_pow_mem n hmem
  exact ⟨M, hM, fun M' hM' => le_antisymm (key _ _ hM' hM) (key _ _ hM hM')⟩

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Powers in a valuation ring with separably closed fraction field.** Let `B` be a domain
integral over a valuation ring `A ⊆ B` whose fraction field is separably closed. Then every
`b ∈ B` has a positive power in `A`: `Frac B / Frac A` is algebraic, hence purely inseparable,
so `b^{q^n} ∈ Frac A`, and it is integral over the integrally closed `A`. -/
theorem exists_pow_mem_of_isSepClosed {A B : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [IsSepClosed (FractionRing A)] (b : B) :
    ∃ n : ℕ, 0 < n ∧ b ^ n ∈ (algebraMap A B).range := by
  let K := FractionRing A
  let L := FractionRing B
  have : Algebra.IsAlgebraic K L := isAlgebraic_of_isFractionRing A B K L
  have : IsPurelyInseparable K L := inferInstance
  obtain ⟨m, k, hk⟩ := IsPurelyInseparable.pow_mem K (ringExpChar K) (algebraMap B L b)
  have hq : 0 < ringExpChar K ^ m := pow_pos (expChar_pos K (ringExpChar K)) m
  refine ⟨ringExpChar K ^ m, hq, ?_⟩
  -- `k` is integral over `A`
  have hint : IsIntegral A (algebraMap K L k) := by
    rw [hk, ← map_pow]
    exact (Algebra.IsIntegral.isIntegral (R := A) (b ^ ringExpChar K ^ m)).map
      (IsScalarTower.toAlgHom A B L)
  have hint' : IsIntegral A k :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).mp hint
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).mp hint'
  refine ⟨a, (IsFractionRing.injective B L) ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A K L, ha, hk, map_pow]

/-- The kernel form of `exists_pow_mem_of_isSepClosed`: if `B` is a domain integral over a
valuation ring `V` such that `Frac(V/𝔭)` is separably closed for the kernel `𝔭` of `V → B`, every
element of `B` has a positive power in the image of `V`. -/
theorem exists_pow_mem_of_isSepClosed_ker {V B : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing B] [IsDomain B] [Algebra V B] [Algebra.IsIntegral V B]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal))) (b : B) :
    ∃ n : ℕ, 0 < n ∧ b ^ n ∈ (algebraMap V B).range := by
  let P := RingHom.ker (algebraMap V B)
  let A := V ⧸ P
  have hP : P.IsPrime := RingHom.ker_isPrime _
  have : IsDomain A := Ideal.Quotient.isDomain P
  have : ValuationRing A :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : Algebra A B := (RingHom.kerLift (algebraMap V B)).toAlgebra
  have : IsScalarTower V A B := IsScalarTower.of_algebraMap_eq fun v => rfl
  have : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (RingHom.kerLift_injective _)
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.tower_top V
  have : IsSepClosed (FractionRing A) := hsep ⟨P, hP⟩
  obtain ⟨n, hn, a, ha⟩ := exists_pow_mem_of_isSepClosed (A := A) b
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨n, hn, v, ha⟩

end Algebra

section Scheme

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- In the spectrum of a local ring, an open set containing the closed point is everything. -/
theorem eq_top_of_closedPoint_mem {R : Type u} [CommRing R] [IsLocalRing R]
    (W : (Spec (CommRingCat.of R)).Opens) (h : IsLocalRing.closedPoint R ∈ W) : W = ⊤ := by
  refine top_unique fun y _ => ?_
  have hy : y ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)
  exact hy.mem_open W.isOpen h

set_option backward.isDefEq.respectTransparency false in
/-- **Closures of algebraic points over a valuation ring with separably closed residue fields
are local** (blueprint `lem:sm-bd-closure-local`(3); ERRATA T11). Let `V` be a valuation ring such
that `Frac(V/𝔭)` is separably closed for every prime `𝔭` (e.g. a valuation ring of a separably
closed field), `g : X → Spec V` proper, `t ⤳ x` with `x` a closed point and `κ(t)` algebraic over
the residue field of `g t`. Then every specialization `z` of `t` is a generization of `x`: the
closure of `t` is finite over `V` (all its points are algebraic over the base, Zariski's main
theorem) and is the spectrum of a local ring (`isLocalRing_of_forall_pow_mem`). -/
theorem specializes_of_specializes_of_isAlgebraicAt
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of V)) [IsProper g] {t x : X} (htx : t ⤳ x)
    (hx : IsClosed ({x} : Set X)) (ht : ValCurves.IsAlgebraicAt g t) {z : X} (hz : t ⤳ z) :
    z ⤳ x := by
  -- the closure of `t` with its reduced structure
  let Z : Closeds X := ⟨closure {t}, isClosed_closure⟩
  let D := Scheme.IdealSheafData.vanishingIdeal Z
  let Y := D.subscheme
  let ι : Y ⟶ X := D.subschemeι
  have : IsReduced Y := Geometry.ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme Z
  have hsupp : (D.support : Set X) = closure {t} := by
    rw [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
    rfl
  have hmem : ∀ w : X, t ⤳ w → w ∈ (D.support : Set X) := fun w hw => by
    rw [hsupp]
    exact specializes_iff_mem_closure.mp hw
  have : IrreducibleSpace Y := by
    have hirr : IsIrreducible (D.support : Set X) := by
      rw [hsupp]
      exact isIrreducible_singleton.closure
    exact Subtype.irreducibleSpace hirr
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced _
  let g' : Y ⟶ Spec (CommRingCat.of V) := ι ≫ g
  -- points of `Y` and specializations
  let t' : Y := ⟨t, hmem t (specializes_refl t)⟩
  let x' : Y := ⟨x, hmem x htx⟩
  let z' : Y := ⟨z, hmem z hz⟩
  have hspec : ∀ a b : Y, ι a ⤳ ι b → a ⤳ b := fun a b h =>
    (ι.isClosedEmbedding.isInducing.specializes_iff).mp h
  -- every point of `Y` is algebraic over the base
  have halg : ∀ y : Y, ValCurves.IsAlgebraicAt g' y := by
    intro y
    have hty : t' ⤳ y := hspec _ _ (by
      have hy : (y.1 : X) ∈ (D.support : Set X) := y.2
      rw [hsupp] at hy
      exact specializes_iff_mem_closure.mpr hy)
    rw [ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero]
    have hle := ValuationRing.fiberTrdeg_le_of_specializes g' hty
    have h0 : ValuationRing.fiberTrdeg g' t' = 0 := by
      rw [ValCurves.fiberTrdeg_comp, ← (ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero g t).mp ht,
        (ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero ι t').mp
          (ValCurves.isAlgebraicAt_of_surjectiveOnStalks ι t'), add_zero]
      rfl
    rw [h0] at hle
    exact le_antisymm hle bot_le
  -- `Y` is finite over `V`
  obtain ⟨W, hW, hfin, -⟩ := ValCurves.exists_isFinite_morphismRestrict_of_isAlgebraicAt g'
    (IsLocalRing.closedPoint V) fun y _ => halg y
  have hWtop : W = ⊤ := eq_top_of_closedPoint_mem W hW
  have : IsFinite g' := by
    exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) (fun _ : Unit => W)
      (by rw [iSup_const, hWtop]) fun _ => hfin
  have : IsAffine Y := isAffine_of_isAffineHom g'
  -- the ring of functions on `Y` is local
  let B := Γ(Y, ⊤)
  let φ : V →+* B := (g'.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  let : Algebra V B := φ.toAlgebra
  have hφfin : φ.Finite := RingHom.Finite.comp (Scheme.Hom.finite_appTop g')
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2)
  have : Algebra.IsIntegral V B := by
    have : Module.Finite V B := hφfin
    infer_instance
  have hlocal : IsLocalRing B :=
    isLocalRing_of_forall_pow_mem (A := V) (B := B) fun b =>
      exists_pow_mem_of_isSepClosed_ker hsep b
  -- every point of `Y` specializes to the closed point `x'`
  have hx' : IsClosed ({x'} : Set Y) := by
    have : ({x'} : Set Y) = ι ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => by rw [h]; rfl,
        fun h => ι.isClosedEmbedding.injective (h.trans (D.subschemeι_apply x').symm)⟩
    rw [this]
    exact hx.preimage ι.continuous
  have hzx : z' ⤳ x' := by
    let e := Y.isoSpec
    have hcl : IsClosed ({e.hom x'} : Set (Spec Γ(Y, ⊤))) := by
      have := e.hom.homeomorph.isClosedMap _ hx'
      rwa [Set.image_singleton] at this
    have hmax : (e.hom x').asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hcl
    have hclosed : e.hom x' = IsLocalRing.closedPoint B :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    have hsp : e.hom z' ⤳ e.hom x' := by
      rw [hclosed]
      exact (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (e.hom z').isPrime.ne_top)
    exact (Scheme.Hom.homeomorph e.hom).isInducing.specializes_iff.mp hsp
  exact hzx.map ι.continuous

/-- **Closedness of a local modification locus** (blueprint `lem:sm-bd-closed-locus`, the step
"`V` is closed in `C̄`" of T:3115–3118; ERRATA T11). Let `V` be a valuation ring with all
`Frac(V/𝔭)` separably closed, `g : X → Spec V` proper, `x` a closed point of `X`, `U ∋ x` open and
`T ⊆ X` a finite set, closed in `U`, of generizations of `x` at which `g` is algebraic. Then `T`
is closed in `X`: the closure of each `t ∈ T` consists of generizations of `x`
(`specializes_of_specializes_of_isAlgebraicAt`), so it lies in `U`, hence in `T`. -/
theorem isClosed_of_forall_specializes
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of V)) [IsProper g] {x : X}
    (hx : IsClosed ({x} : Set X)) (U : X.Opens) (hxU : x ∈ U) {T : Set X} (hTfin : T.Finite)
    (hTU : IsClosed (((↑) : U → X) ⁻¹' T))
    (hT : ∀ t ∈ T, t ⤳ x ∧ ValCurves.IsAlgebraicAt g t) : IsClosed T := by
  have hsub : ∀ t ∈ T, closure {t} ⊆ T := by
    intro t ht z hz
    have htz : t ⤳ z := specializes_iff_mem_closure.mpr hz
    have hzx : z ⤳ x :=
      specializes_of_specializes_of_isAlgebraicAt hsep g (hT t ht).1 hx (hT t ht).2 htz
    have hzU : z ∈ U := hzx.mem_open U.isOpen hxU
    have htU : t ∈ U := (hT t ht).1.mem_open U.isOpen hxU
    have hsp : (⟨t, htU⟩ : U) ⤳ ⟨z, hzU⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp htz
    exact hsp.mem_closed hTU ht
  have hT' : T = ⋃ t ∈ T, closure {t} := by
    refine subset_antisymm (fun t ht => ?_) (Set.iUnion₂_subset hsub)
    exact Set.mem_biUnion ht (subset_closure (Set.mem_singleton t))
  rw [hT']
  exact hTfin.isClosed_biUnion fun t _ => isClosed_closure

end Scheme

end DeJongAlterations.StableModification.BlowDown
