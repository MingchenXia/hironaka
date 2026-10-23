/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureLocalPoints
import DeJongAlterations.StableModification.BlowDown.ClosureComponent
import DeJongAlterations.StableModification.BlowDown.NodalReduced
import DeJongAlterations.StableModification.BlowDown.NormalizationCurve
import DeJongAlterations.StableModification.Cohomology.SteinReduced

/-!
# The closed fibre of a component of a nodal curve is reduced

Let `R` be an integrally closed local domain, `g : Y → Spec R` a nodal curve and `z` a generic
point of `Y`. The closed fibre of the closure of `z` (with any reduced closed subscheme structure)
is reduced (`isReduced_closedFibre_of_isClosedImmersion`). Affine-locally, for an affine open
`U ∋ z` the ideal `𝔭_z + 𝔪_R Γ(U, 𝒪_Y)` is radical (`isRadical_fibreIdeal`): radicality is
checked at the maximal ideals (`mem_of_forall_isMaximal`), where it is the field `reduced` of lane
T44E's `LocalStructure` (`localStructure_of_isNodalCurve`), applied to the minimal prime of `z`
in the local ring and to the reduced closed fibre of `Y` (`DeJong.IsNodalCurve.isReduced_pullback`,
`Cohomology.isRadical_map_maximalIdeal_of_isReduced`).

This is part (2) of the closure-component lemma (M. Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), `references/temkin10-stable-modification/source/
semi-stable.tex`, proof of Lemma 4.4.4, T:3164–3166; blueprint `lem:sm-bd-closure-component`(2)),
in the form `lem:sm-bdcl-reduced` of `sm-blow-down-closure-local.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Topology

namespace DeJongAlterations.StableModification.BlowDown.ClosureLocal

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Radical

variable {A : Type*} [CommRing A]

/-- **Membership is local at the maximal ideals**: if for every maximal ideal `𝔪 ⊇ J` some
`s ∉ 𝔪` has `s x ∈ J`, then `x ∈ J`. -/
theorem mem_of_forall_isMaximal (J : Ideal A) (x : A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → J ≤ 𝔪 → ∃ s ∉ 𝔪, s * x ∈ J) : x ∈ J := by
  by_contra hx
  have hK : Submodule.colon J {x} ≠ ⊤ := by
    intro hK
    apply hx
    have h1 : (1 : A) ∈ Submodule.colon J {x} := hK ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, smul_eq_mul, one_mul] at h1
    exact h1
  obtain ⟨𝔪, h𝔪, hK𝔪⟩ := Ideal.exists_le_maximal _ hK
  by_cases hJ : J ≤ 𝔪
  · obtain ⟨s, hs, hsx⟩ := h 𝔪 h𝔪 hJ
    exact hs (hK𝔪 (Submodule.mem_colon_singleton.mpr (by rw [smul_eq_mul]; exact hsx)))
  · obtain ⟨j, hj, hj𝔪⟩ := Set.not_subset.mp hJ
    exact hj𝔪 (hK𝔪 (Submodule.mem_colon_singleton.mpr (by
      rw [smul_eq_mul]
      exact J.mul_mem_right x hj)))

end Radical

section Sections

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R))

/-- The algebra map of `sectionsAlgebra g U` is the structure coefficient map `R → Γ(U, 𝒪_Y)`. -/
theorem algebraMap_sectionsAlgebra (U : Y.Opens) :
    @algebraMap R Γ(Y, U) _ _ (sectionsAlgebra g U) =
      Cohomology.sectionsRingHom (Cohomology.structureCoeff g) (le_top : U ≤ ⊤) := by
  ext a
  simp [Cohomology.sectionsRingHom, Cohomology.structureCoeff, Scheme.Hom.appLE,
    RingHom.algebraMap_toAlgebra]

variable {U : Y.Opens} (hU : IsAffineOpen U)

/-- The ideal `𝔭_z + 𝔪_R Γ(U, 𝒪_Y)` of the closed fibre of the closure of `z ∈ U`. -/
abbrev fibreIdeal [IsLocalRing R] {z : Y} (hzU : z ∈ U) : Ideal Γ(Y, U) :=
  (hU.primeIdealOf ⟨z, hzU⟩).asIdeal ⊔
    (maximalIdeal R).map (Cohomology.sectionsRingHom (Cohomology.structureCoeff g) (le_top : U ≤ ⊤))

variable [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [DeJong.IsNodalCurve g]

/-- **The local step**: at a point `y ∈ U` of the closed fibre of the closure of a generic point
`z ∈ U`, an element with a power in `𝔭_z + 𝔪_R Γ(U)` lies in it after multiplication by some
`s ∉ 𝔭_y` (`LocalStructure.reduced`). -/
theorem exists_mul_mem_fibreIdeal {z : Y} (hzU : z ∈ U) (hz : ∀ ξ, ξ ⤳ z → ξ = z) {y : Y}
    (hyU : y ∈ U) (hJ : fibreIdeal g hU hzU ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) {x : Γ(Y, U)}
    {k : ℕ} (hx : x ^ k ∈ fibreIdeal g hU hzU) :
    ∃ s ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal, s * x ∈ fibreIdeal g hU hzU := by
  let := sectionsAlgebra g U
  have hmap : (maximalIdeal R).map
      (Cohomology.sectionsRingHom (Cohomology.structureCoeff g) (le_top : U ≤ ⊤)) =
      (maximalIdeal R).map (algebraMap R Γ(Y, U)) := by
    rw [algebraMap_sectionsAlgebra]
  have hred : IsReduced (pullback g (Spec.map (CommRingCat.ofHom (residue R)))) :=
    DeJong.IsNodalCurve.isReduced_pullback g _ _
  have hrad0 : ((maximalIdeal R).map (algebraMap R Γ(Y, U))).IsRadical := by
    rw [← hmap]
    exact Cohomology.isRadical_map_maximalIdeal_of_isReduced g hU
  -- `y` lies over the closed point
  have hy : (g y).asIdeal = maximalIdeal R := by
    rw [← comap_primeIdealOf g hU y hyU]
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _
      (hU.primeIdealOf ⟨y, hyU⟩).isPrime.ne_top)) ?_
    rw [← Ideal.map_le_iff_le_comap, ← hmap]
    exact le_sup_right.trans hJ
  have hLS := localStructure_of_isNodalCurve g hU y hyU hy
  have hzy : z ⤳ y := (primeIdealOf_le_iff hU hzU hyU).mp (le_sup_left.trans hJ)
  have hmin := mem_minimalPrimes_locIdeal hU hyU hzU hzy hz
  have hred0 : _root_.IsReduced (LocRing hU hyU ⧸
      (maximalIdeal R).map (algebraMap R (LocRing hU hyU))) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, IsScalarTower.algebraMap_eq R Γ(Y, U)
      (LocRing hU hyU), ← Ideal.map_map]
    change (((maximalIdeal R).map (algebraMap R Γ(Y, U))).map
      (algebraMap Γ(Y, U) (LocRing hU hyU))).radical ≤ _
    rw [← IsLocalization.map_radical (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
      (LocRing hU hyU), hrad0.radical]
  have hred1 := hLS.reduced _ hmin hred0
  have hJA : (fibreIdeal g hU hzU).map (algebraMap Γ(Y, U) (LocRing hU hyU)) =
      locIdeal hU hyU hzU ⊔ (maximalIdeal R).map (algebraMap R (LocRing hU hyU)) := by
    rw [fibreIdeal, Ideal.map_sup, hmap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hradA : ((fibreIdeal g hU hzU).map (algebraMap Γ(Y, U) (LocRing hU hyU))).IsRadical := by
    rw [hJA, Ideal.isRadical_iff_quotient_reduced]
    exact hred1
  have hxA : algebraMap Γ(Y, U) (LocRing hU hyU) x ∈
      (fibreIdeal g hU hzU).map (algebraMap Γ(Y, U) (LocRing hU hyU)) :=
    hradA ⟨k, by rw [← map_pow]; exact Ideal.mem_map_of_mem _ hx⟩
  obtain ⟨s, hs, hsx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl (LocRing hU hyU) _ x).mp hxA
  exact ⟨s, hs, hsx⟩

/-- **The closed fibre of a component is reduced, affine-locally** (blueprint
`lem:sm-bdcl-reduced`): for a generic point `z` of the nodal curve `Y` over the integrally closed
local domain `R` and an affine open `U ∋ z`, the ideal `𝔭_z + 𝔪_R Γ(U, 𝒪_Y)` is radical. -/
theorem isRadical_fibreIdeal {z : Y} (hzU : z ∈ U) (hz : ∀ ξ, ξ ⤳ z → ξ = z) :
    (fibreIdeal g hU hzU).IsRadical := by
  rintro x ⟨k, hk⟩
  refine mem_of_forall_isMaximal _ x fun 𝔪 h𝔪 hJ => ?_
  have hyU : hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩ ∈ U := fromSpec_mem hU _
  have hy𝔪 : (hU.primeIdealOf ⟨hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩, hyU⟩).asIdeal = 𝔪 :=
    congrArg PrimeSpectrum.asIdeal (primeIdealOf_fromSpec hU _ hyU)
  rw [← hy𝔪] at hJ ⊢
  exact exists_mul_mem_fibreIdeal g hU hzU hz hyU hJ hk

/-- **The closed fibre of the closure of a generic point of a nodal curve is reduced** (blueprint
`lem:sm-bdcl-reduced`): for `R` an integrally closed local domain, `g : Y → Spec R` nodal, `z` a
generic point of `Y` and `i : T → Y` a closed immersion of a reduced scheme with image the
closure of `z`, the closed fibre `T ×_R κ` of `i ≫ g` is reduced. -/
theorem isReduced_closedFibre_of_isClosedImmersion {z : Y} (hz : ∀ ξ, ξ ⤳ z → ξ = z)
    {T : Scheme.{u}} [IsReduced T] (i : T ⟶ Y) [IsClosedImmersion i]
    (hi : Set.range i = closure {z}) :
    IsReduced (pullback (i ≫ g) (Spec.map (CommRingCat.ofHom (residue R)))) := by
  refine isReduced_closedFibre_of_forall_exists_isRadical (i ≫ g) fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := i x) (U := ⊤) trivial
  refine ⟨i ⁻¹ᵁ U, hU.preimage i, hxU, ?_⟩
  have hzU : z ∈ U := by
    have hix : i x ∈ closure {z} := hi ▸ Set.mem_range_self x
    exact (specializes_iff_mem_closure.mpr hix).mem_open U.2 hxU
  have hJ := isRadical_fibreIdeal g hU hzU hz
  rw [sectionsRingHom_comp_appLE i g U (i ⁻¹ᵁ U) le_rfl, ← Ideal.map_map]
  set φ := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom
  have hφ : Function.Surjective φ := by
    have h := i.app_surjective U hU
    rwa [Scheme.Hom.app_eq_appLE] at h
  have hpre : hU.fromSpec ⁻¹' closure {z} = closure {hU.primeIdealOf ⟨z, hzU⟩} := by
    rw [hU.fromSpec.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hU.fromSpec_primeIdealOf]
  have hker : RingHom.ker φ = (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    have h1 := i.ker_apply ⟨U, hU⟩
    rw [Scheme.Hom.app_eq_appLE] at h1
    rw [← h1, ClosureComponent.ker_eq_vanishingIdeal_of_isReduced i,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure (Set.range i)) = _
    rw [hi, closure_closure, hpre, PrimeSpectrum.vanishingIdeal_closure,
      PrimeSpectrum.vanishingIdeal_singleton]
  set I := (maximalIdeal R).map
    (Cohomology.sectionsRingHom (Cohomology.structureCoeff g) (le_top : U ≤ ⊤))
  have hcm : Ideal.comap φ (Ideal.map φ I) = fibreIdeal g hU hzU := by
    rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, hker, sup_comm]
  rintro b ⟨k, hk⟩
  obtain ⟨a, rfl⟩ := hφ b
  have ha : a ∈ fibreIdeal g hU hzU := by
    refine hJ ⟨k, ?_⟩
    rw [← hcm, Ideal.mem_comap, map_pow]
    exact hk
  rw [← hcm] at ha
  exact ha

end Sections

end DeJongAlterations.StableModification.BlowDown.ClosureLocal
