/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalCoefficientPolynomialBaseChange
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Category.ModuleCat.Free

/-! # One genuine coefficient-algebra open for nearby original normal module freeness -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalCoefficientFunctionAlgebra HironakaRelativeNormalUniformLocalization
  HironakaRelativeNormalCoefficientPolynomialBaseChange HironakaRelativeNormalUniformTruncations

attribute [local instance] coefficientSubalgebraRing

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- One actual nonvanishing open makes every entire nearby original associated module free. -/
theorem exists_original_nearby_associated_free_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U, Module.Free (HolGerm (ComplexModel d))
        (originalNormalAssociatedGraded d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a)))) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨B, _hB, h0, C, _hC, hD, _hDf, W, hW, h0W, hWB, ρ, Q, _hhom, hρ, hideal⟩ :=
    exists_original_common_domain_coefficient_initial_family d t I hI
  let D := coefficientOriginAlgebra d B h0 C
  let : IsDomain D := hD
  let : Field (FractionRing D) := FractionRing.field D
  let H : Ideal (MvPolynomial (Fin t) D) := Ideal.span (range Q)
  let b := uniformLeadingDenominator (K := FractionRing D) t (MonomialOrder.degLex (σ := Fin t)) H
  have hb : b ≠ 0 := uniformLeadingDenominator_ne_zero _ _ _
  obtain ⟨c, hcb⟩ := Ideal.Quotient.mk_surjective b
  let g : ComplexModel d → ℂ := (C.val c).val
  have hc0 : ((coefficientGermHom d B 0 h0).comp C.val) c ≠ 0 := by
    intro hz
    have hc : c ∈ coefficientOriginKernel d B h0 C := hz
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    rw [hcb] at he
    exact hb he
  have hg0 : (g : Germ (𝓝 (0 : ComplexModel d)) ℂ) ≠ 0 := by
    intro hz
    apply hc0
    apply Subtype.ext
    change (Germ.coeRingHom (𝓝 (0 : ComplexModel d))) (g ∘ actualAffineTranslation d 0) = 0
    have hid : g ∘ actualAffineTranslation d 0 = g := by
      funext z
      simp only [Function.comp_apply, actualAffineTranslation, zero_add]
    rw [hid]
    exact hz
  let U := {a : ComplexModel d | a ∈ W ∧ g a ≠ 0}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hcont : ContinuousAt g a := ((C.val c).property a (hWB ha.1)).self_of_nhds.continuousAt
    filter_upwards [hW.mem_nhds ha.1, hcont.eventually_ne ha.2] with z hz hgz
    exact ⟨hz, hgz⟩
  have hmeet : ∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty := by
    intro V hV
    by_contra hn
    apply hg0
    apply Germ.coe_eq.mpr
    filter_upwards [hV, hW.mem_nhds h0W] with a haV haW
    by_contra hga
    exact hn ⟨a, haV, haW, hga⟩
  refine ⟨U, hU, hmeet, ?_⟩
  intro a ha
  have hvalue : (ρ a ha.1) b = coefficientGermHom d B a (hWB ha.1) (C.val c) := by
    rw [← hcb]
    exact congrArg (fun f : C →ₐ[ℂ] HolGerm (ComplexModel d) => f c) (hρ a ha.1)
  have hunit : IsUnit ((ρ a ha.1) b) := by
    apply (HolGerm.isUnit_iff_eval_ne_zero ((ρ a ha.1) b)).mpr
    rw [hvalue]
    change g (actualAffineTranslation d a 0) ≠ 0
    simpa only [actualAffineTranslation_zero] using ha.2
  have hp := moduleFree_coefficient_image_at_uniform_denominator (K := FractionRing D)
    t (MonomialOrder.degLex (σ := Fin t)) H (ρ a ha.1).toRingHom hunit
  change Module.Free (HolGerm (ComplexModel d))
    (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸
      Ideal.map (MvPolynomial.map (ρ a ha.1).toRingHom) (Ideal.span (range Q))) at hp
  rw [hideal a ha.1] at hp
  let : Module.Free (HolGerm (ComplexModel d))
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ originalNormalInitialIdeal d t
        (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a)))) := hp
  exact Module.Free.of_equiv (originalNormalAssociatedGradedQuotientEquiv d t _)

/-- Every literal original degree layer is an image of a finite homogeneous polynomial module. -/
theorem moduleFinite_originalNormalGradedPiece (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) := by
  let := tangentAlgebra d t
  let : Module.Finite (HolGerm (ComplexModel d))
      (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d)) q) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg _ _ q)
  exact Module.Finite.of_surjective (homogeneousNormalSymbolMap d t I q)
    (homogeneousNormalSymbolMap_surjective d t I q)

/-- Genuine finite degree layers are free over the local base ring if their whole direct sum is free. -/
theorem all_originalNormalGradedPiece_finite_free_of_associated_free (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    Module.Free (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t I) →
      ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  intro hfree q
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t I) := hfree
  let : Module.Projective (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) :=
    (Module.Projective.directSum_iff.mp
      (inferInstance : Module.Projective (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t I))) q
  let : Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) :=
    moduleFinite_originalNormalGradedPiece d t I q
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

/-- Only original coherent input gives one actual open for all nearby original finite free degrees. -/
theorem exists_original_nearby_all_degree_finite_free_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U, ∀ q : ℕ,
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) := by
  let := tangentAlgebra d t
  obtain ⟨U, hU, hmeet, hfree⟩ := exists_original_nearby_associated_free_open d t I hI
  exact ⟨U, hU, hmeet, fun a ha =>
    all_originalNormalGradedPiece_finite_free_of_associated_free d t _ (hfree a ha)⟩

private theorem actual_short_exact_middle_free {R L M N : Type} [CommRing R]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N] [Module.Free R L] [Module.Free R N]
    (g : L →ₗ[R] M) (h : M →ₗ[R] N) (hg : Function.Injective g)
    (hh : Function.Surjective h) (ex : Function.Exact g h) : Module.Free R M := by
  let S := ModuleCat.shortComplexOfCompEqZero g h ex.linearMap_comp_eq_zero
  have hs := ModuleCat.shortComplex_shortExact S ex hg hh
  exact ModuleCat.free_shortExact hs

private theorem actual_exact_middle_finite {R L M N : Type} [CommRing R]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N] [Module.Finite R L] [Module.Finite R N]
    (g : L →ₗ[R] M) (h : M →ₗ[R] N)
    (hh : Function.Surjective h) (ex : Function.Exact g h) : Module.Finite R M := by
  exact Module.Finite.of_exact (f := g) (g := h) ex hh

/-- Actual original finite free layers give every whole original power quotient finite free. -/
theorem all_originalNormalTruncation_finite_free_of_graded_free (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    (∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) ∧
      Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q)) →
      ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  intro hdegree q
  induction q with
  | zero =>
    let := originalNormalTruncation_zero_subsingleton d t I
    let b0 : Module.Basis PEmpty.{1} (HolGerm (ComplexModel d)) (originalNormalTruncation d t I 0) :=
      Module.Basis.empty _
    exact ⟨Module.Free.of_basis b0, Module.Finite.of_basis b0⟩
  | succ q ih =>
    let := ih.1
    let := ih.2
    let := (hdegree q).1
    let := (hdegree q).2
    let g := originalNormalTruncationPieceInclusion d t I q
    let h := (originalNormalTruncationMap d t I q).toLinearMap
    have hg : Function.Injective g := originalNormalTruncationPieceInclusion_injective d t I q
    have hh : Function.Surjective h := originalNormalTruncationMap_surjective d t I q
    have he : Function.Exact g h := originalNormalTruncation_exact d t I q
    exact ⟨actual_short_exact_middle_free g h hg hh he,
      actual_exact_middle_finite g h hh he⟩

/-- One original-input actual open works for every nearby whole original normal-power truncation. -/
theorem exists_original_nearby_all_truncation_finite_free_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U, ∀ q : ℕ,
        Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) := by
  let := tangentAlgebra d t
  obtain ⟨U, hU, hmeet, hdegree⟩ := exists_original_nearby_all_degree_finite_free_open d t I hI
  exact ⟨U, hU, hmeet, fun a ha =>
    all_originalNormalTruncation_finite_free_of_graded_free d t _ (hdegree a ha)⟩

end
end Hironaka.HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
