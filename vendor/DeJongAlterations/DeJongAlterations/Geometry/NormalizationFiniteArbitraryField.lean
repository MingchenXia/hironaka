import DeJongAlterations.Algebra.IntegralClosureFiniteType
import DeJongAlterations.Geometry.NormalizationBirational

/-!
# The actual global normalization over an arbitrary field

The new arbitrary-field finiteness theorem applies in the original scheme
function field. The actual affine normalization pullback squares give global
finiteness, and the native common-denominator argument gives an actual birational
modification. Normalized curves are regular over any ground field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.NormalizationFiniteArbitraryField

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

open NormalizationGluing

section Integral

variable [IsIntegral X]

/-- Arbitrary-field finiteness in the original scheme's actual common function field. -/
theorem finite_integralClosure_functionField (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : X.affineOpens) [Nonempty U.1] :
    Module.Finite Γ(X, U.1) (integralClosure Γ(X, U.1) X.functionField) := by
  let := (NormalizationFinite.affineCoefficientMap p U).toAlgebra
  let : Algebra.FiniteType k Γ(X, U.1) := NormalizationFinite.affineSections_finiteType p U
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  let : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  exact DeJongAlterations.Algebra.IntegralClosureFiniteType.finite_integralClosure
    k Γ(X, U.1) X.functionField

/-- The original affine normalization map is finite without any perfectness hypothesis. -/
theorem affineNormalizationMap_isFinite (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : X.affineOpens) [Nonempty U.1] : IsFinite (NormalizationFinite.affineNormalizationMap U) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (finite_integralClosure_functionField p U)

/-- Normalized affine charts of actual curves are regular over an arbitrary field. -/
theorem integralClosure_functionField_isRegular (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : X.affineOpens) [Nonempty U.1] (hdim : topologicalKrullDim X ≤ 1) :
    IsRegularScheme (Spec (.of (integralClosure Γ(X, U.1) X.functionField))) := by
  let := (NormalizationFinite.affineCoefficientMap p U).toAlgebra
  let : Algebra.FiniteType k Γ(X, U.1) := NormalizationFinite.affineSections_finiteType p U
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  let : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  let : Ring.KrullDimLE 1 Γ(X, U.1) := NormalizationFinite.affineSections_krullDimLE_one U hdim
  let : Ring.DimensionLEOne Γ(X, U.1) := ⟨fun _ hP ↦ hP.isMaximal_of_ne_bot ‹_›⟩
  let : Ring.DimensionLEOne (integralClosure Γ(X, U.1) X.functionField) := inferInstance
  let : IsNoetherianRing (integralClosure Γ(X, U.1) X.functionField) :=
    DeJongAlterations.Algebra.IntegralClosureFiniteType.isNoetherianRing_integralClosure
      k Γ(X, U.1) X.functionField
  let : IsIntegrallyClosed (integralClosure Γ(X, U.1) X.functionField) :=
    AffineCurveAlteration.isIntegrallyClosed_integralClosure Γ(X, U.1) X.functionField
  exact isRegularScheme_spec_of_isIntegrallyClosed_of_krullDimLE_one _

/-- Genuine normalization pullback squares descend actual affine finiteness. -/
theorem normalizationStructure_isFinite (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsFinite (normalizationStructure X) := by
  apply IsZariskiLocalAtTarget.of_openCover (NormalizationFinite.nonemptyAffineCoordinateOpenCover X)
  intro U
  let V : NonemptyAffineOpen X := U
  let h := (isPullback_chart V).flip
  change IsFinite (Limits.pullback.snd (normalizationStructure X) V.1.2.fromSpec)
  rw [← h.isoPullback_inv_snd]
  let : IsFinite (affineStructure V) := affineNormalizationMap_isFinite p ⟨V.1.1, V.1.2⟩
  infer_instance

/-- The same actual global normalization is a finite dominant alteration. -/
theorem normalizationStructure_isAlteration (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsAlteration (normalizationStructure X) := by
  let : IsIntegral (normalization X) := NormalizationFinite.isIntegral_normalization
  let : IsFinite (normalizationStructure X) := normalizationStructure_isFinite p
  let : IsDominant (normalizationStructure X) := NormalizationFinite.normalizationStructure_isDominant
  exact isAlteration_of_isFinite _

/-- Actual normalized chart stalks give actual global curve regularity. -/
theorem normalization_isRegular (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1) : IsRegularScheme (normalization X) := by
  intro x
  let C := normalizationCover X
  obtain ⟨y, hy⟩ := C.covers x
  let U : NonemptyAffineOpen X := C.idx x
  let : IsRegularLocalRing ((C.X U).presheaf.stalk y) :=
    integralClosure_functionField_isRegular p ⟨U.1.1, U.1.2⟩ hdim y
  have hr : IsRegularLocalRing ((normalization X).presheaf.stalk (C.f U y)) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso ((C.f U).stalkMap y)).symm.commRingCatIsoToRingEquiv
  rw [hy] at hr
  exact hr

/-- An actual nonzero affine isomorphism open is produced by the common-denominator theorem. -/
theorem exists_affine_isomorphism_open (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : NonemptyAffineOpen X) :
    ∃ a : Γ(X, U.1.1), a ≠ 0 ∧ IsIso (affineStructure U ∣_ PrimeSpectrum.basicOpen a) := by
  let : IsDomain Γ(X, U.1.1) := IsIntegral.component_integral U.1.1
  let : IsFractionRing Γ(X, U.1.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  let : Module.Finite Γ(X, U.1.1) (closureRing U) :=
    finite_integralClosure_functionField p ⟨U.1.1, U.1.2⟩
  exact NormalizationBirational.exists_specMap_isomorphism_open
    (integralClosure Γ(X, U.1.1) X.functionField)

private theorem structure_restrict_image_isIso (U : NonemptyAffineOpen X)
    (a : Γ(X, U.1.1)) [IsIso (affineStructure U ∣_ PrimeSpectrum.basicOpen a)] :
    IsIso (normalizationStructure X ∣_ U.1.2.fromSpec ''ᵁ PrimeSpectrum.basicOpen a) := by
  let i := U.1.2.fromSpec
  let j := chartInclusion X U
  let g := affineStructure U
  let π := normalizationStructure X
  let W := i ''ᵁ PrimeSpectrum.basicOpen a
  have hpre : i ⁻¹ᵁ W = PrimeSpectrum.basicOpen a := i.preimage_image_eq _
  have hi : W ≤ i.opensRange := i.image_le_opensRange _
  have hj : π ⁻¹ᵁ W ≤ j.opensRange := by
    rw [chartInclusion_opensRange]
    exact π.preimage_mono (hi.trans U.1.2.opensRange_fromSpec.le)
  let : IsIso (i ∣_ W) := isIso_morphismRestrict_of_le_opensRange i W hi
  let : IsIso (g ∣_ i ⁻¹ᵁ W) := by rw [hpre]; infer_instance
  let : IsIso ((g ≫ i) ∣_ W) := by rw [morphismRestrict_comp]; infer_instance
  have hcomp : j ≫ π = g ≫ i := chartInclusion_structure U
  let : IsIso ((j ≫ π) ∣_ W) := by rw [hcomp]; infer_instance
  let : IsIso (j ∣_ π ⁻¹ᵁ W) := isIso_morphismRestrict_of_le_opensRange j _ hj
  let : IsIso ((j ∣_ π ⁻¹ᵁ W) ≫ π ∣_ W) := by rw [← morphismRestrict_comp]; infer_instance
  exact IsIso.of_isIso_comp_left (f := j ∣_ π ⁻¹ᵁ W) (π ∣_ W)

/-- A genuine nonempty target open on which the actual whole normalization is an isomorphism. -/
theorem exists_isomorphism_open (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ IsIso (normalizationStructure X ∣_ W) := by
  let U : NonemptyAffineOpen X :=
    (NormalizationFinite.nonemptyAffineCoordinateOpenCover X).idx (Classical.choice inferInstance)
  obtain ⟨a, ha, hi⟩ := exists_affine_isomorphism_open p U
  let : IsIso (affineStructure U ∣_ PrimeSpectrum.basicOpen a) := hi
  refine ⟨U.1.2.fromSpec ''ᵁ PrimeSpectrum.basicOpen a, ?_, structure_restrict_image_isIso U a⟩
  let : IsDomain Γ(X, U.1.1) := IsIntegral.component_integral U.1.1
  have hne : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Γ(X, U.1.1))).Nonempty := by
    refine ⟨⊥, ?_⟩
    change a ∉ (⊥ : Ideal Γ(X, U.1.1))
    simpa using ha
  obtain ⟨x, hx⟩ := hne
  exact ⟨U.1.2.fromSpec x, ⟨x, hx, rfl⟩⟩

/-- Birationality is witnessed by the actual dense source and target restriction opens. -/
theorem normalizationStructure_birationalOver (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    Scheme.BirationalOver (normalizationStructure X) (𝟙 X) := by
  let : IsIntegral (normalization X) := NormalizationFinite.isIntegral_normalization
  obtain ⟨W, hW, hi⟩ := exists_isomorphism_open p
  let : IsIso (normalizationStructure X ∣_ W) := hi
  have hpre : (normalizationStructure X ⁻¹ᵁ W : Set (normalization X)).Nonempty := by
    obtain ⟨y, hy⟩ := hW
    obtain ⟨x, _⟩ := (normalizationStructure X ∣_ W).surjective ⟨y, hy⟩
    exact ⟨x.val, x.property⟩
  refine ⟨{
    source := normalizationStructure X ⁻¹ᵁ W
    dense_source := (normalizationStructure X ⁻¹ᵁ W).isOpen.dense hpre
    target := W
    dense_target := W.isOpen.dense hW
    iso := asIso (normalizationStructure X ∣_ W) }, ?_⟩
  change (normalizationStructure X ∣_ W) ≫ W.ι ≫ 𝟙 X =
    (normalizationStructure X ⁻¹ᵁ W).ι ≫ normalizationStructure X
  rw [Category.comp_id, morphismRestrict_ι]

/-- The constructed native global normalization is an actual proper birational modification. -/
theorem normalizationStructure_isModification (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsModification (normalizationStructure X) := by
  let : IsFinite (normalizationStructure X) := normalizationStructure_isFinite p
  exact {
    sourceIntegral := NormalizationFinite.isIntegral_normalization
    targetIntegral := inferInstance
    birational := normalizationStructure_birationalOver p }

/-- Generic étaleness holds for the same actual normalization map over any ground field. -/
theorem normalizationStructure_isGenericallyEtale (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsGenericallyEtale (normalizationStructure X) :=
  isGenericallyEtale_of_birationalOver_id _ (normalizationStructure_birationalOver p)

end Integral

/-- The same actual normalization is again a variety over the original arbitrary field. -/
theorem normalization_isVariety (p : X ⟶ Spec (.of k)) [IsVariety p] :
    IsVariety (normalizationStructure X ≫ p) := by
  let : IsIntegral (normalization X) := NormalizationFinite.isIntegral_normalization
  let : IsFinite (normalizationStructure X) := normalizationStructure_isFinite p
  exact .mk

/-- Every arbitrary-field curve variety has its actual normalization as a regular alteration. -/
theorem hasRegularAlteration_curve (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hdim : topologicalKrullDim X ≤ 1) : HasRegularAlteration p := by
  exact ⟨normalization X, normalizationStructure X ≫ p, normalizationStructure X,
    normalization_isVariety p, rfl, normalizationStructure_isAlteration p,
    normalization_isRegular p hdim⟩

/-- The actual arbitrary-field curve normalization is also a generically étale alteration. -/
theorem hasRegularGenericallyEtaleAlteration_curve (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hdim : topologicalKrullDim X ≤ 1) : HasRegularGenericallyEtaleAlteration p := by
  exact ⟨normalization X, normalizationStructure X ≫ p, normalizationStructure X,
    normalization_isVariety p, rfl, normalizationStructure_isAlteration p,
    normalization_isRegular p hdim, normalizationStructure_isGenericallyEtale p⟩

end DeJongAlterations.Geometry.NormalizationFiniteArbitraryField
