/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OrdinaryCompletionLocalization

/-!
# The local rings of the normalization of a curve are discrete valuation rings

Let `A` be a one-dimensional Noetherian local ring (the local ring `𝒪_{C,x}` of a reduced curve at a
closed point), `B ⊇ A` a finite `A`-algebra (the semilocal ring `𝒪_{C̃,x̃}` of the normalization)
which is integrally closed in an `A`-algebra `L ⊇ B` (the product of the residue fields at the
generic points) in which an element `s ∈ 𝔪_A` is invertible. This file proves that **the
localizations of `B` at its maximal ideals (the local rings of `C̃` at the points of `x̃`) are
discrete valuation rings** (`isDiscreteValuationRing_localization`). This is the regularity of the
normalization used in M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010) (`references/temkin10-stable-modification/source/semi-stable.tex`, App. B, l. 4381–4387),
where the completed local ring of an ordinary point is computed from the branches `k[[t]]` of the
normalization.

## Main results

* `krullDimLE_one_of_isIntegral`: an integral extension of a ring of dimension `≤ 1` has
  dimension `≤ 1` (incomparability).
* `isDiscreteValuationRing_of_isIntegrallyClosedIn`: a one-dimensional Noetherian local ring which
  is integrally closed in an extension `L` in which some `s ∈ 𝔪` is invertible is a discrete
  valuation ring. The argument is the one of CRV4's
  `OrdinaryCompletion.false_of_isIntegrallyClosedIn_of_formalNode` (`A_s` is reduced,
  zero-dimensional and without nontrivial idempotents, hence a field, and `A` is integrally closed
  in it), stopped before its last step.
* `exists_algebraMap_eq_of_isIntegral_localization`: integral closedness of `B` in `L` localizes at
  a prime of `B`.
* `isDiscreteValuationRing_localization`: the localizations of `B` at its maximal ideals are
  discrete valuation rings.

Blueprint: `sm-curves-fields-ordinary-gluing.tex`, `lem:sm-og-dimension`, `lem:sm-og-dvr`.
-/

namespace DeJongAlterations.StableModification.CurvesField.OrdinaryGluing

open IsLocalRing
open DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion

set_option autoImplicit false

noncomputable section

section Dimension

/-- **An integral extension of a ring of dimension `≤ 1` has dimension `≤ 1`**: a prime `q` of `B`
whose contraction is maximal is maximal, and otherwise the contraction is minimal and, by
incomparability, so is `q`. -/
theorem krullDimLE_one_of_isIntegral {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] [Ring.KrullDimLE 1 A] : Ring.KrullDimLE 1 B := by
  refine Ring.KrullDimLE.mk₁ fun q hq => ?_
  by_cases hmax : (q.comap (algebraMap A B)).IsMaximal
  · exact Or.inr (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q hmax)
  · have hmin : q.comap (algebraMap A B) ∈ minimalPrimes A :=
      ((Ring.krullDimLE_one_iff.1 inferInstance) _ (Ideal.comap_isPrime _ q)).resolve_right hmax
    refine Or.inl ⟨⟨hq, bot_le⟩, fun q' hq' hle => ?_⟩
    rcases eq_or_lt_of_le hle with h | hlt
    · exact h.ge
    · exfalso
      have : q'.IsPrime := hq'.1
      have hlt' := Ideal.IsIntegral.comap_lt_comap (R := A) hlt
      exact hlt'.not_ge (hmin.2 ⟨Ideal.comap_isPrime _ q', bot_le⟩ hlt'.le)

end Dimension

section DVR

/-- **A one-dimensional Noetherian local ring which is integrally closed in an extension inverting
an element of its maximal ideal is a discrete valuation ring.** Let `D` be local Noetherian of
dimension `≤ 1`, `s ∈ 𝔪_D`, and `D ⊆ L` with `s` invertible in `L` and `D` integrally closed in
`L`. Then `D_s` is reduced, zero-dimensional and has no nontrivial idempotents (they are integral
over `D`, hence in the local ring `D`), so it is a field; `D` is integrally closed in it, hence an
integrally closed domain of dimension one, i.e. a discrete valuation ring. (The argument of CRV4's
`OrdinaryCompletion.false_of_isIntegrallyClosedIn_of_formalNode`.) -/
theorem isDiscreteValuationRing_of_isIntegrallyClosedIn {D : Type*} [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] [Ring.KrullDimLE 1 D] {s : D} (hs : s ∈ maximalIdeal D) {L : Type*}
    [CommRing L] [Algebra D L] (hDL : Function.Injective (algebraMap D L))
    (hsL : IsUnit (algebraMap D L s))
    (hint : ∀ y : L, IsIntegral D y → ∃ a : D, algebraMap D L a = y) :
    ∃ _ : IsDomain D, IsDiscreteValuationRing D := by
  -- `s` is a non-zero-divisor
  have hsnz : s ∈ nonZeroDivisors D := by
    refine mem_nonZeroDivisors_iff_right.2 fun a ha => hDL ?_
    rw [map_zero]
    have h : algebraMap D L a * algebraMap D L s = 0 := by rw [← map_mul, ha, map_zero]
    exact (hsL.mul_left_eq_zero).1 h
  let Ds := Localization.Away s
  have hinjD : Function.Injective (algebraMap D Ds) :=
    IsLocalization.injective Ds (Submonoid.powers_le.2 hsnz)
  let j : Ds →+* L := IsLocalization.Away.lift s hsL
  have hj : ∀ a, j (algebraMap D Ds a) = algebraMap D L a := fun a =>
    IsLocalization.lift_eq _ a
  have hjinj : Function.Injective j := by
    refine (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers s) j).2 fun x y => ?_
    rw [hj, hj]
    exact ⟨fun h => by rw [hinjD h], fun h => by rw [hDL h]⟩
  have hintDs : ∀ y : Ds, IsIntegral D y → ∃ a : D, algebraMap D Ds a = y := by
    intro y hy
    have hcomp : (algebraMap D L).comp (RingHom.id D) = j.comp (algebraMap D Ds) := by
      ext a
      exact (hj a).symm
    obtain ⟨a, ha⟩ := hint (j y) (IsIntegral.map_of_comp_eq (RingHom.id D) j hcomp hy)
    exact ⟨a, hjinj (by rw [hj, ha])⟩
  have : Nontrivial L := hDL.nontrivial
  have hnt : Nontrivial Ds := j.domain_nontrivial
  -- `D` is reduced: `nil(D) = s · nil(D)`, then Nakayama
  have hred : IsReduced D := by
    have hN : nilradical D = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal D) (nilradical D)
        (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
      intro n hn
      have hy : IsNilpotent (IsLocalization.mk' Ds n (⟨s, Submonoid.mem_powers s⟩ :
          Submonoid.powers s)) := by
        obtain ⟨m, hm⟩ := (mem_nilradical.1 hn)
        refine ⟨m, ?_⟩
        rw [← IsLocalization.mk'_pow, hm, IsLocalization.mk'_zero]
      obtain ⟨a, ha⟩ := hintDs _ (isIntegral_of_isNilpotent hy)
      have hna : n = a * s := by
        rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul] at ha
        exact hinjD (by rw [ha, map_mul])
      have hanil : a ∈ nilradical D :=
        mem_nilradical.2 ((IsNilpotent.map_iff hinjD).1 (ha ▸ hy))
      rw [hna, mul_comm, Ideal.smul_eq_mul]
      exact Ideal.mul_mem_mul hs hanil
    refine ⟨fun x hx => ?_⟩
    have : x ∈ nilradical D := hx
    rw [hN] at this
    exact this
  have : IsReduced Ds := inferInstanceAs (IsReduced (Localization (Submonoid.powers s)))
  -- `D_s` is zero-dimensional
  have hdim0 : Ring.KrullDimLE 0 Ds := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    have hsM : s ∉ M.comap (algebraMap D Ds) := fun h =>
      hM.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
    have hqM : (M.comap (algebraMap D Ds)).IsPrime := Ideal.comap_isPrime _ M
    have hmin : M.comap (algebraMap D Ds) ∈ minimalPrimes D := by
      rcases Ring.krullDimLE_one_iff.1 inferInstance _ hqM with h | h
      · exact h
      · exact absurd ((IsLocalRing.eq_maximalIdeal h) ▸ hs) hsM
    have hle : P.comap (algebraMap D Ds) ≤ M.comap (algebraMap D Ds) := Ideal.comap_mono hPM
    have heq : P.comap (algebraMap D Ds) = M.comap (algebraMap D Ds) :=
      le_antisymm hle (hmin.2 ⟨Ideal.comap_isPrime _ P, bot_le⟩ hle)
    have heq' : Ideal.under D P = Ideal.under D M := heq
    have : P = M := by
      rw [← IsLocalization.map_under (Submonoid.powers s) Ds P,
        ← IsLocalization.map_under (Submonoid.powers s) Ds M, heq']
    exact this ▸ hM
  have hart : IsArtinianRing Ds :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, hdim0⟩
  -- `D_s` has no nontrivial idempotents, hence is local, hence a field
  have hloc : IsLocalRing Ds := by
    classical
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨M, hM⟩ := Ideal.exists_maximal Ds
    refine ⟨M, hM, fun N hN => ?_⟩
    by_contra hNM
    let E := IsArtinianRing.equivPi Ds
    let I₁ : MaximalSpectrum Ds := ⟨M, hM⟩
    let I₂ : MaximalSpectrum Ds := ⟨N, hN⟩
    have hI : I₁ ≠ I₂ := fun h => hNM (congrArg MaximalSpectrum.asIdeal h).symm
    let x : Ds := E.symm (Pi.single I₁ 1)
    have hx : IsIdempotentElem x := by
      change x * x = x
      rw [← map_mul]
      congr 1
      ext I
      by_cases hI' : I = I₁
      · subst hI'
        simp
      · simp [hI']
    obtain ⟨a, ha⟩ := hintDs x (isIntegral_of_isIdempotentElem hx)
    have hia : IsIdempotentElem a := hinjD (by rw [map_mul, ha]; exact hx.eq)
    have hEx : E x = Pi.single I₁ 1 := E.apply_symm_apply _
    rcases eq_zero_or_eq_one_of_isIdempotentElem hia with h0 | h1
    · have h0' : E x I₁ = 0 := by rw [← ha, h0, map_zero, map_zero]; rfl
      rw [hEx, Pi.single_eq_same] at h0'
      have : Nontrivial (Ds ⧸ I₁.asIdeal) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
      exact one_ne_zero h0'
    · have h1' : E x I₂ = 1 := by rw [← ha, h1, map_one, map_one]; rfl
      rw [hEx, Pi.single_eq_of_ne hI.symm] at h1'
      have : Nontrivial (Ds ⧸ I₂.asIdeal) := Ideal.Quotient.nontrivial_iff.2 hN.ne_top
      exact zero_ne_one h1'
  have hfield : IsField Ds := IsArtinianRing.isField_of_isReduced_of_isLocalRing Ds
  let : Field Ds := hfield.toField
  -- `D` is an integrally closed domain
  have hdom : IsDomain D := hinjD.isDomain (algebraMap D Ds)
  have hic : IsIntegrallyClosed D := by
    rw [isIntegrallyClosed_iff (FractionRing D)]
    intro x hx
    let g : FractionRing D →+* Ds := IsFractionRing.lift hinjD
    have hg : ∀ a, g (algebraMap D (FractionRing D) a) = algebraMap D Ds a := fun a =>
      IsFractionRing.lift_algebraMap hinjD a
    have hcomp : (algebraMap D Ds).comp (RingHom.id D) =
        g.comp (algebraMap D (FractionRing D)) := by
      ext a
      exact (hg a).symm
    obtain ⟨a, ha⟩ := hintDs (g x) (IsIntegral.map_of_comp_eq (RingHom.id D) g hcomp hx)
    exact ⟨a, g.injective (by rw [hg, ha])⟩
  have hnf : ¬ IsField D := by
    intro h
    have hm : maximalIdeal D = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 h
    have : s = 0 := by rw [← Ideal.mem_bot, ← hm]; exact hs
    exact (nonZeroDivisors.ne_zero hsnz) this
  -- so `D` is a discrete valuation ring
  have key := (IsDiscreteValuationRing.TFAE D hnf).out 0 3
  refine ⟨hdom, key.2 ⟨hic, maximalIdeal D,
    ⟨fun h => hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h), inferInstance⟩, ?_⟩⟩
  rintro P ⟨hP, hPp⟩
  exact IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)

end DVR

section Localization

variable {B L : Type*} [CommRing B] [CommRing L] [Algebra B L]

/-- **Integral closedness localizes at a prime of the base**: if every element of `L` integral over
`B` comes from `B`, then every element of `L_𝔫` integral over `B_𝔫` comes from `B_𝔫`. (CRV4's
`OrdinaryCompletion.mem_range_localizedAlgHom_of_isIntegral` for `B = R`.) -/
theorem exists_algebraMap_eq_of_isIntegral_localization
    (hint : ∀ y : L, IsIntegral B y → ∃ b : B, algebraMap B L b = y) (n : Ideal B) [n.IsPrime]
    (y : Localization (Algebra.algebraMapSubmonoid L n.primeCompl))
    (hy : IsIntegral (Localization.AtPrime n) y) :
    ∃ d : Localization.AtPrime n,
      algebraMap (Localization.AtPrime n)
        (Localization (Algebra.algebraMapSubmonoid L n.primeCompl)) d = y := by
  obtain ⟨⟨m, hm⟩, hmy⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization n.primeCompl
      (Rₘ := Localization.AtPrime n) y hy
  obtain ⟨⟨t, ⟨_, ⟨u, hu, rfl⟩⟩⟩, ht⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid L n.primeCompl)
      ((⟨m, hm⟩ : n.primeCompl) • y)
  have hut : algebraMap L (Localization (Algebra.algebraMapSubmonoid L n.primeCompl)) t =
      algebraMap B (Localization (Algebra.algebraMapSubmonoid L n.primeCompl)) u *
        ((⟨m, hm⟩ : n.primeCompl) • y) := by
    rw [← ht, IsScalarTower.algebraMap_apply B L, mul_comm, IsLocalization.mk'_spec]
  have hint₁ : IsIntegral B
      (algebraMap L (Localization (Algebra.algebraMapSubmonoid L n.primeCompl)) t) := by
    rw [hut]
    exact (isIntegral_algebraMap).mul hmy
  obtain ⟨m', hm', hm't⟩ :=
    IsLocalization.exists_isIntegral_smul_of_isIntegral_map n.primeCompl hint₁
  obtain ⟨b, hb⟩ := hint _ hm't
  have hden : m' * (u * m) ∈ n.primeCompl :=
    n.primeCompl.mul_mem hm' (n.primeCompl.mul_mem hu hm)
  refine ⟨IsLocalization.mk' _ b (⟨m' * (u * m), hden⟩ : n.primeCompl), ?_⟩
  rw [IsLocalization.algebraMap_mk' (S := L), IsLocalization.mk'_eq_iff_eq_mul]
  have hb' : algebraMap B L b = m' • t := hb
  rw [hb', Algebra.smul_def, map_mul, hut, Submonoid.smul_def, Algebra.smul_def,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_mul, map_mul]
  have e : ((⟨m, hm⟩ : n.primeCompl) : B) = m := rfl
  rw [e]
  ring

end Localization

section Semilocal

variable {A : Type*} {B : Type*} {L : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [CommRing B] [Algebra A B] [Module.Finite A B] [CommRing L] [Algebra A L]

/-- **The localizations of the normalization at its maximal ideals are discrete valuation rings.**
Let `A` be a one-dimensional Noetherian local ring, `B` a finite `A`-algebra, `ι : B → L` an
injective `A`-algebra map such that every element of `L` integral over `A` lies in `ι(B)`, and
`s ∈ 𝔪_A` invertible in `L`. Then for every maximal ideal `𝔫` of `B`, `B_𝔫` is a discrete valuation
ring. -/
theorem isDiscreteValuationRing_localization (ι : B →ₐ[A] L) (hι : Function.Injective ι)
    (hint : ∀ y : L, IsIntegral A y → y ∈ ι.range) {s : A} (hs : s ∈ maximalIdeal A)
    (hsL : IsUnit (algebraMap A L s)) (n : Ideal B) [hn : n.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime n), IsDiscreteValuationRing (Localization.AtPrime n) := by
  let _ : Algebra B L := ι.toRingHom.toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  have : Algebra.IsIntegral A B := inferInstance
  have : IsNoetherianRing B := isNoetherian_of_tower A inferInstance
  have : Ring.KrullDimLE 1 B := krullDimLE_one_of_isIntegral (A := A)
  have : Ring.KrullDimLE 1 (Localization.AtPrime n) := krullDimLE_localization n
  -- `s` lies in `𝔫`
  have hcomap : n.comap (algebraMap A B) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)
  have hsn : algebraMap A B s ∈ n := by
    rw [← Ideal.mem_comap, hcomap]
    exact hs
  have hsm : algebraMap B (Localization.AtPrime n) (algebraMap A B s) ∈
      maximalIdeal (Localization.AtPrime n) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ n _).2 hsn
  refine isDiscreteValuationRing_of_isIntegrallyClosedIn hsm
    (L := Localization (Algebra.algebraMapSubmonoid L n.primeCompl))
    (algebraMap_localization_injective n (S := L) (by exact hι))
    (isUnit_algebraMap_localization (T := L) n
      (by rw [← IsScalarTower.algebraMap_apply]; exact hsL))
    fun y hy => exists_algebraMap_eq_of_isIntegral_localization (fun z hz => ?_) n y hy
  obtain ⟨b, hb⟩ := hint z (isIntegral_trans (R := A) (A := B) z hz)
  exact ⟨b, hb⟩

end Semilocal

end

end DeJongAlterations.StableModification.CurvesField.OrdinaryGluing
