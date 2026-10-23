import DeJongAlterations.Geometry.NormalizationFinite
import DeJongAlterations.Geometry.AffineBlowupIsomorphism
import DeJongAlterations.Modification
import Mathlib.RingTheory.Localization.Integer

/-!
# The actual normalization as a birational modification

Finite generation supplies a common nonzero denominator for the actual integral
closure inside the original function field. The canonical localized coefficient
map, and hence the actual restricted scheme morphism, is an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

namespace DeJongAlterations.Geometry.NormalizationBirational

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section CommonDenominator

variable {R F : Type u} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] (B : Subalgebra R F) [Module.Finite R B]

/-- Finitely many actual module generators in the common fraction field have
a common nonzero denominator, which clears every element of the subalgebra. -/
theorem exists_common_denominator :
    ∃ a : R, a ≠ 0 ∧ ∀ b : B, ∃ r : R,
      algebraMap R F r = algebraMap R F a * (b : F) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples R⁰ s (fun b : B => (b : F))
  have hall (b : B) : IsLocalization.IsInteger R ((a : R) • (b : F)) := by
    have hb : b ∈ Submodule.span R (s : Set B) := by rw [hs]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb => exact ha b hb
    | zero => simpa using (IsLocalization.isInteger_zero (R := R) (S := F))
    | add b c hb hc hib hic =>
      change IsLocalization.IsInteger R ((a : R) • ((b : F) + (c : F)))
      rw [smul_add]
      exact IsLocalization.isInteger_add hib hic
    | smul r b hb hib =>
      change IsLocalization.IsInteger R ((a : R) • (r • (b : F)))
      rw [smul_comm]
      exact IsLocalization.isInteger_smul hib
  refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp a.property, ?_⟩
  intro b
  obtain ⟨r, hr⟩ := hall b
  exact ⟨r, by simpa only [Algebra.smul_def] using hr⟩

/-- The whole canonical coefficient map becomes bijective on an actual
nonzero principal localization. No generic comparison map is supplied. -/
theorem exists_awayMap_bijective :
    ∃ a : R, a ≠ 0 ∧ Function.Bijective (Localization.awayMap (algebraMap R B) a) := by
  obtain ⟨a, ha, hall⟩ := exists_common_denominator B
  refine ⟨a, ha, ?_, ?_⟩
  · apply Localization.awayMap_injective_iff.mpr
    intro r hr
    have hzero : r = 0 := IsFractionRing.injective R F (by
      simpa using congrArg (fun b : B => (b : F)) hr)
    exact ⟨0, by simp [hzero]⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro b
    obtain ⟨r, hr⟩ := hall b
    refine ⟨r, 1, ?_⟩
    apply Subtype.ext
    simpa using hr

/-- A finite subalgebra of the original fraction field has an actual
nonzero principal open over which its canonical spectrum map is an isomorphism. -/
theorem exists_specMap_isomorphism_open :
    ∃ a : R, a ≠ 0 ∧ IsIso
      (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ PrimeSpectrum.basicOpen a) := by
  obtain ⟨a, ha, hbij⟩ := exists_awayMap_bijective B
  let e := RingEquiv.ofBijective (Localization.awayMap (algebraMap R B) a) hbij
  let : IsIso (Spec.map (CommRingCat.ofHom
      (Localization.awayMap (algebraMap R B) a))) := by
    change IsIso (Spec.map e.toCommRingCatIso.hom)
    infer_instance
  refine ⟨a, ha, ?_⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R B)) a)).mpr inferInstance

end CommonDenominator

open NormalizationGluing

section Integral

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- The actual affine normalization has an internally produced nonzero
isomorphism open over the original perfect-field coefficient structure. -/
theorem exists_affine_isomorphism_open [PerfectField k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (U : NonemptyAffineOpen X) :
    ∃ a : Γ(X, U.1.1), a ≠ 0 ∧ IsIso (affineStructure U ∣_ PrimeSpectrum.basicOpen a) := by
  let : IsDomain Γ(X, U.1.1) := IsIntegral.component_integral U.1.1
  let : IsFractionRing Γ(X, U.1.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  let : Module.Finite Γ(X, U.1.1) (closureRing U) :=
    NormalizationFinite.finite_integralClosure_functionField p ⟨U.1.1, U.1.2⟩
  exact exists_specMap_isomorphism_open (integralClosure Γ(X, U.1.1) X.functionField)

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
  have : IsIso (i ∣_ W) := isIso_morphismRestrict_of_le_opensRange i W hi
  have : IsIso (g ∣_ i ⁻¹ᵁ W) := by rw [hpre]; infer_instance
  have : IsIso ((g ≫ i) ∣_ W) := by
    rw [morphismRestrict_comp]
    infer_instance
  have hcomp : j ≫ π = g ≫ i := chartInclusion_structure U
  have : IsIso ((j ≫ π) ∣_ W) := by rw [hcomp]; infer_instance
  have : IsIso (j ∣_ π ⁻¹ᵁ W) := isIso_morphismRestrict_of_le_opensRange j _ hj
  have : IsIso ((j ∣_ π ⁻¹ᵁ W) ≫ π ∣_ W) := by
    rw [← morphismRestrict_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (f := j ∣_ π ⁻¹ᵁ W) (π ∣_ W)

/-- The actual native global normalization is an isomorphism over an
internally constructed nonempty open of the original scheme. -/
theorem exists_isomorphism_open [PerfectField k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ IsIso (normalizationStructure X ∣_ W) := by
  let U : NonemptyAffineOpen X :=
    (NormalizationFinite.nonemptyAffineCoordinateOpenCover X).idx
      (Classical.choice inferInstance)
  obtain ⟨a, ha, hi⟩ := exists_affine_isomorphism_open p U
  let : IsIso (affineStructure U ∣_ PrimeSpectrum.basicOpen a) := hi
  refine ⟨U.1.2.fromSpec ''ᵁ PrimeSpectrum.basicOpen a, ?_,
    structure_restrict_image_isIso U a⟩
  let : IsDomain Γ(X, U.1.1) := IsIntegral.component_integral U.1.1
  have hne : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Γ(X, U.1.1))).Nonempty := by
    refine ⟨⊥, ?_⟩
    change a ∉ (⊥ : Ideal Γ(X, U.1.1))
    simpa using ha
  obtain ⟨x, hx⟩ := hne
  exact ⟨U.1.2.fromSpec x, ⟨x, hx, rfl⟩⟩

/-- Native birationality of the same actual normalization map over its
original scheme, witnessed by the actual restricted morphism. -/
theorem normalizationStructure_birationalOver [PerfectField k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] :
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

/-- The actual finite normalization is a native proper birational modification. -/
theorem normalizationStructure_isModification [PerfectField k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] : IsModification (normalizationStructure X) := by
  let : IsFinite (normalizationStructure X) := NormalizationFinite.normalizationStructure_isFinite p
  exact {
    sourceIntegral := NormalizationFinite.isIntegral_normalization
    targetIntegral := inferInstance
    birational := normalizationStructure_birationalOver p }

/-- Generic étaleness holds on the actual dense source open of the native
birational partial isomorphism for this same normalization structure map. -/
theorem normalizationStructure_isGenericallyEtale [PerfectField k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] : IsGenericallyEtale (normalizationStructure X) :=
  isGenericallyEtale_of_birationalOver_id _ (normalizationStructure_birationalOver p)

end Integral

/-- The actual normalization gives a generically étale regular alteration of
every perfect-field variety of dimension at most one, including nonaffine curves. -/
theorem hasRegularGenericallyEtaleAlteration_curve {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hdim : topologicalKrullDim X ≤ 1) : HasRegularGenericallyEtaleAlteration p := by
  exact ⟨normalization X, normalizationStructure X ≫ p, normalizationStructure X,
    NormalizationFinite.normalization_isVariety p, rfl,
    NormalizationFinite.normalizationStructure_isAlteration p,
    NormalizationFinite.normalization_isRegular p hdim,
    normalizationStructure_isGenericallyEtale p⟩

end DeJongAlterations.Geometry.NormalizationBirational
