/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureLocalChart
import DeJongAlterations.StableModification.BlowDown.NumericalDescentSmooth
import DeJongAlterations.StableModification.Curves.SemistableNormalScheme
import DeJongAlterations.StableModification.DeJong.NodalBaseChange

/-!
# The local structure of a nodal curve over an integrally closed local domain

Let `R` be an integrally closed local domain and `g : Y → Spec R` a nodal curve. For an affine
open `U ⊆ Y` and a point `y ∈ U` over the closed point of `Spec R`, the local ring of
`Γ(U, 𝒪_Y)` at `y` has `LocalStructure` (`localStructure_of_isNodalCurve`), and it is a domain if
`g` is smooth at `y` (`isDomain_localization_of_isSmoothAt`). The proof follows lane SS3's
`Curves.SemistableNormal.isNormalScheme_of_isNodalCurve`: a closed point of a geometric fibre over
`y` is a smooth point or a node, and the local structure on a smaller chart `Spec B_f`
(`exists_away_localStructure_of_isFormalNode`, resp. lane SS3's
`exists_away_isIntegrallyClosed_of_spanFinrank_le_one`) is transported to `Γ(U, 𝒪_Y)`.

Blueprint: `sm-blow-down-unconditional.tex`, `prop:sm-bdu-local-structure`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TensorProduct

namespace DeJongAlterations.StableModification.BlowDown.ClosureLocal

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Curves.SemistableNormal Curves.SemistableOpen

section Scheme

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Curves.SemistableOpen.locallyOfFinitePresentation_spec

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R))

/-- The algebra structure `R → Γ(U, 𝒪_Y)` of an open `U` over `Spec R`. -/
abbrev sectionsAlgebra (U : Y.Opens) : Algebra R Γ(Y, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra

/-- The square `Spec Γ(U) → Y → Spec R` of an affine open, with the algebra structure
`sectionsAlgebra`. -/
theorem fromSpec_comp_eq' {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra g U
    hU.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U))) ≫ 𝟙 _ := by
  letI := sectionsAlgebra g U
  rw [Category.comp_id, ← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The sections over an affine open of a flat morphism to `Spec R` are flat over `R`. -/
theorem flat_sections [Flat g] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra g U
    Module.Flat R Γ(Y, U) := by
  letI := sectionsAlgebra g U
  have h := HasRingHomProperty.appLE @Flat g inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  rw [← RingHom.flat_algebraMap_iff]
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mpr h

/-- The sections over an affine open of a morphism locally of finite presentation to `Spec R`
are finitely presented over `R`. -/
theorem finitePresentation_sections [LocallyOfFinitePresentation g] {U : Y.Opens}
    (hU : IsAffineOpen U) :
    letI := sectionsAlgebra g U
    Algebra.FinitePresentation R Γ(Y, U) := by
  letI := sectionsAlgebra g U
  have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation g inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h' : (algebraMap R Γ(Y, U)).FinitePresentation :=
    (RingHom.finitePresentation_respectsIso.cancel_left_isIso _ _).mpr h
  exact h'

variable [IsDomain R] [IsIntegrallyClosed R] [DeJong.IsNodalCurve g]

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- **Charts of a nodal curve at a point** (after lane SS3): for an affine open `U ∋ y`, the
local ring of `Γ(U)` at `y` is that of a localization `Γ(U)_f` at a closed point `z₁` of a
geometric fibre of `Spec Γ(U)_f`, for any `f` outside the prime of `y`. -/
theorem exists_away_chart {U : Y.Opens} (hU : IsAffineOpen U) (y : Y) (hyU : y ∈ U) :
    letI := sectionsAlgebra g U
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra R K)
      (z : Ideal (K ⊗[R] Γ(Y, U))) (_ : z.IsMaximal),
      z.comap (Algebra.TensorProduct.includeRight : Γ(Y, U) →ₐ[R] K ⊗[R] Γ(Y, U)).toRingHom =
          (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∧
      ((DeJong.IsSmoothAt g y →
          (maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 1) ∧
        ((maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 1 ∨ IsFormalNode K z)) ∧
      ∀ f : Γ(Y, U), f ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
        ∃ z₁ : Ideal (K ⊗[R] Localization.Away f), ∃ _ : z₁.IsMaximal,
          (z₁.comap (Algebra.TensorProduct.includeRight :
              Localization.Away f →ₐ[R] K ⊗[R] Localization.Away f).toRingHom).comap
              (algebraMap Γ(Y, U) (Localization.Away f)) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∧
          ringKrullDim (Localization.AtPrime z₁) = 1 ∧
          ((maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 1 ∨
            (IsFormalNode K z → IsFormalNode K z₁)) := by
  letI := sectionsAlgebra g U
  have : Module.Flat R Γ(Y, U) := flat_sections g hU
  have : Algebra.FinitePresentation R Γ(Y, U) := finitePresentation_sections g hU
  have hsq := fromSpec_comp_eq' g hU
  set 𝔭 := hU.primeIdealOf ⟨y, hyU⟩
  have hx𝔭 : hU.fromSpec 𝔭 = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  obtain ⟨K, _, _, _, z, hzmax, hz𝔭⟩ := exists_geometricPoint (R := R) 𝔭.asIdeal
  set a : Spec (.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ 𝟙 _
  have ha : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ 𝟙 _ = a := rfl
  set zp : PrimeSpectrum (K ⊗[R] Γ(Y, U)) := ⟨z, hzmax.isPrime⟩
  have hzc : IsClosed ({zp} : Set (Spec (.of (K ⊗[R] Γ(Y, U))))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hzmax
  set y' := tensorChart g hsq ha zp
  have hyx : pullback.fst g a y' = y := by
    rw [← jB_comap_eq g hsq ha zp]
    have : PrimeSpectrum.comap (algebraMap Γ(Y, U) (K ⊗[R] Γ(Y, U))) zp = 𝔭 := PrimeSpectrum.ext hz𝔭
    rw [this, hx𝔭]
  have hy' : IsClosed ({y'} : Set (pullback (C := Scheme.{u}) g a)) :=
    Curves.isClosed_image_of_isClosed (tensorChart g hsq ha) (tensorChart_snd g hsq ha) hzc
  have hpure := DeJong.IsNodalCurve.pureGeometricFibers (g := g) K a
  have hdimz : ringKrullDim (Localization.AtPrime z) = 1 := by
    have hpureT := pure_of_etale (q' := pullback.snd g a) (tensorChart g hsq ha) hpure
    have hdim := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT zp hzc
    let := Scheme.stalkAlgebra
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] Γ(Y, U))))) zp
    let ε := (Geometry.NodeCompletedLocalSpecLocalization.stalkEquiv K (K ⊗[R] Γ(Y, U)) zp).toRingEquiv
    rw [← ringKrullDim_eq_of_ringEquiv ε]
    exact hdim
  have hsmooth : DeJong.IsSmoothAt (pullback.snd g a) y' →
      (maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 1 := by
    intro hs
    have hzs := mem_smoothLocus_of_tensorChart g hsq ha zp hs
    have hpureT := pure_of_etale (q' := pullback.snd g a) (tensorChart g hsq ha) hpure
    have hdim := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT zp hzc
    exact (mem_smoothLocus_spec_iff zp hdim).mp hzs
  refine ⟨K, inferInstance, inferInstance, inferInstance, z, hzmax, hz𝔭, ⟨fun hsm => hsmooth ?_,
    ?_⟩, fun f hf => ?_⟩
  · apply DeJong.isSmoothAt_pullback_snd
    rw [hyx]
    exact hsm
  · rcases DeJong.IsNodalCurve.geometricNodes (g := g) K a y' hy' with hs | hn
    · exact Or.inl (hsmooth hs)
    · exact Or.inr ((isGeometricOrdinaryDoublePoint_spec_iff zp).mp
        (isGeometricOrdinaryDoublePoint_of_tensorChart g hsq ha zp hzc hn))
  · have hsq₁ := localization_chart_sq g hsq f
    have hxB₁ : pullback.fst g a y' ∈ Set.range
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away f))) ≫ hU.fromSpec) := by
      rw [hyx, ← hx𝔭]
      exact mem_range_localization_chart f 𝔭 hf
    obtain ⟨z₁, hz₁y, hz₁c⟩ := exists_tensorChart_eq g hsq₁ ha y' hy' hxB₁
    have hz₁max : z₁.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal z₁).mp hz₁c
    refine ⟨z₁.asIdeal, hz₁max, ?_, ?_, ?_⟩
    · have hxz₁ := jB_comap_eq g hsq₁ ha z₁
      rw [hz₁y, hyx, ← hx𝔭, Scheme.Hom.comp_apply] at hxz₁
      have := hU.fromSpec.isOpenEmbedding.injective hxz₁
      exact congrArg PrimeSpectrum.asIdeal this
    · have : Module.Flat R (Localization.Away f) := Module.Flat.trans _ Γ(Y, U) _
      have : Algebra.FinitePresentation R (Localization.Away f) :=
        Algebra.FinitePresentation.trans _ Γ(Y, U) _
      have hpureT₁ := pure_of_etale (q' := pullback.snd g a)
        (tensorChart g (localization_chart_sq g hsq f) ha) hpure
      have hdim₁ := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT₁ z₁ hz₁c
      let := Scheme.stalkAlgebra
        (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] Localization.Away f)))) z₁
      let ε := (Geometry.NodeCompletedLocalSpecLocalization.stalkEquiv K
        (K ⊗[R] Localization.Away f) z₁).toRingEquiv
      rw [← ringKrullDim_eq_of_ringEquiv ε]
      exact hdim₁
    · rcases DeJong.IsNodalCurve.geometricNodes (g := g) K a y' hy' with hs | hn
      · exact Or.inl (hsmooth hs)
      · refine Or.inr fun _ => ?_
        have : Module.Flat R (Localization.Away f) := Module.Flat.trans _ Γ(Y, U) _
        have : Algebra.FinitePresentation R (Localization.Away f) :=
          Algebra.FinitePresentation.trans _ Γ(Y, U) _
        have hz₁n := isGeometricOrdinaryDoublePoint_of_tensorChart g
          (localization_chart_sq g hsq f) ha z₁ hz₁c (hz₁y ▸ hn)
        exact (isGeometricOrdinaryDoublePoint_spec_iff z₁).mp hz₁n

omit [IsDomain R] [IsIntegrallyClosed R] [DeJong.IsNodalCurve g] in
/-- The prime of a point of an affine open lies over its image in `Spec R`. -/
theorem comap_primeIdealOf {U : Y.Opens} (hU : IsAffineOpen U) (y : Y) (hyU : y ∈ U) :
    letI := sectionsAlgebra g U
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.comap (algebraMap R Γ(Y, U)) = (g y).asIdeal := by
  letI := sectionsAlgebra g U
  have hsq := fromSpec_comp_eq' g hU
  have h : (hU.fromSpec ≫ g) (hU.primeIdealOf ⟨y, hyU⟩) = g y := by
    rw [Scheme.Hom.comp_apply, hU.fromSpec_primeIdealOf ⟨y, hyU⟩]
  rw [hsq, Category.comp_id] at h
  exact congrArg PrimeSpectrum.asIdeal h

/-- **At a smooth point the local ring of a nodal curve over an integrally closed domain is a
domain** (lane SS3's `exists_away_isIntegrallyClosed_of_spanFinrank_le_one`). -/
theorem isDomain_localization_of_isSmoothAt {U : Y.Opens} (hU : IsAffineOpen U) (y : Y)
    (hyU : y ∈ U) (hsm : DeJong.IsSmoothAt g y) :
    letI := sectionsAlgebra g U
    IsDomain (Localization.AtPrime (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) := by
  letI := sectionsAlgebra g U
  have : Module.Flat R Γ(Y, U) := flat_sections g hU
  have : Algebra.FinitePresentation R Γ(Y, U) := finitePresentation_sections g hU
  obtain ⟨K, _, _, _, z, _, hz𝔭, ⟨hsmz, -⟩, hf⟩ := exists_away_chart g hU y hyU
  obtain ⟨f, hfz, hnext⟩ := exists_away_isIntegrallyClosed_of_spanFinrank_le_one z (hsmz hsm)
  rw [hz𝔭] at hfz
  obtain ⟨z₁, _, hz₁, hdim₁, -⟩ := hf f hfz
  have h₁ := hnext K z₁ hdim₁
  have h₂ := isDomain_isIntegrallyClosed_localization_localization (Submonoid.powers f) _ h₁
  exact (isDomain_isIntegrallyClosed_of_eq hz₁ h₂).1

/-- **The local structure of a nodal curve over an integrally closed local domain** (blueprint
`prop:sm-bdu-local-structure`): at a point `y` of an affine open `U` lying over the closed point,
the local ring of `Γ(U)` has `LocalStructure`. -/
theorem localStructure_of_isNodalCurve [IsLocalRing R] {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hyU : y ∈ U) (hy : (g y).asIdeal = maximalIdeal R) :
    letI := sectionsAlgebra g U
    LocalStructure R (Localization.AtPrime (hU.primeIdealOf ⟨y, hyU⟩).asIdeal)
      (maximalIdeal R) := by
  letI := sectionsAlgebra g U
  have : Module.Flat R Γ(Y, U) := flat_sections g hU
  have : Algebra.FinitePresentation R Γ(Y, U) := finitePresentation_sections g hU
  obtain ⟨K, _, _, _, z, _, hz𝔭, ⟨-, hdich⟩, hf⟩ := exists_away_chart g hU y hyU
  by_cases hsm : (maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 1
  · obtain ⟨f, hfz, hnext⟩ := exists_away_isIntegrallyClosed_of_spanFinrank_le_one z hsm
    rw [hz𝔭] at hfz
    obtain ⟨z₁, _, hz₁, hdim₁, -⟩ := hf f hfz
    have h₁ := hnext K z₁ hdim₁
    have h₂ := isDomain_isIntegrallyClosed_localization_localization (Submonoid.powers f) _ h₁
    have := (isDomain_isIntegrallyClosed_of_eq hz₁ h₂).1
    exact LocalStructure.of_isDomain
  · have hnode := hdich.resolve_left hsm
    obtain ⟨f, hfz, hnext⟩ := exists_away_localStructure_of_isFormalNode z hnode
    rw [hz𝔭] at hfz
    obtain ⟨z₁, _, hz₁, -, hor⟩ := hf f hfz
    have hz₁n := (hor.resolve_left hsm) hnode
    have hz₁R : (z₁.comap (Algebra.TensorProduct.includeRight :
        Localization.Away f →ₐ[R] K ⊗[R] Localization.Away f).toRingHom).comap
          (algebraMap R (Localization.Away f)) = maximalIdeal R := by
      rw [IsScalarTower.algebraMap_eq R Γ(Y, U) (Localization.Away f), ← Ideal.comap_comap, hz₁,
        comap_primeIdealOf g hU y hyU, hy]
    have h₁ := hnext K z₁ hz₁n hz₁R
    have h₂ := LocalStructure.of_localization_localization (maximalIdeal R) (Submonoid.powers f) _ h₁
    exact LocalStructure.of_eq (maximalIdeal R) hz₁ h₂

end Scheme

end DeJongAlterations.StableModification.BlowDown.ClosureLocal
