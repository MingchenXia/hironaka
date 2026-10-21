/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainCoefficientAlgebra
import Hironaka.Resolution.HironakaRelativeNormalCanonicalCentreFreeness

/-! # One true real nonvanishing open for all original nearby normal degrees
Complete two-node mathematics precedes code. Original regularity/coherence
supply actual coefficient quotient domains and every nearby original kernel.
ONE uniform denominator gives ALL degrees on ONE actual open. Canonical centre
actions are independently descended on associated layers, never truncations.
-/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainNearbyFreeness
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainCoefficientAlgebra
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalCoefficientFunctionAlgebra HironakaRelativeNormalUniformLocalization
  HironakaRelativeNormalCoefficientPolynomialBaseChange HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
  HironakaRelativeNormalCentreScalars HironakaRelativeNormalCanonicalCentreFreeness
attribute [local instance] coefficientSubalgebraRing

section Original
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- ONLY original real-centre inputs construct one uniform actual nonvanishing free open for ALL original nearby associated modules. -/
theorem exists_original_regular_real_nearby_associated_free_open
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel d), IsOpen U ∧
        (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
        (∀ a ∈ U, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        ∀ a ∈ U, Module.Free (HolGerm (ComplexModel d))
          (originalNormalAssociatedGraded d t
            (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a)))) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨Φ,hsrc,h0Φ,hflat,B,_hB,h0,hpoint,C0,_hC,hD,_hDf,W,hW,h0W,hWB,ρ,Q,_hhom,hρ,hideal⟩ :=
    exists_original_regular_real_common_domain_initial_family C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  let D := coefficientOriginAlgebra d B h0 C0
  let : IsDomain D := hD
  let : Field (FractionRing D) := FractionRing.field D
  let H : Ideal (MvPolynomial (Fin t) D) := Ideal.span (range Q)
  let b := uniformLeadingDenominator (K := FractionRing D) t (MonomialOrder.degLex (σ := Fin t)) H
  have hb : b ≠ 0 := uniformLeadingDenominator_ne_zero _ _ _
  obtain ⟨c, hcb⟩ := Ideal.Quotient.mk_surjective b
  let g : ComplexModel d → ℂ := (C0.val c).val
  have hc0 : ((coefficientGermHom d B 0 h0).comp C0.val) c ≠ 0 := by
    intro hz
    have hc : c ∈ coefficientOriginKernel d B h0 C0 := hz
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
    have hcont : ContinuousAt g a := ((C0.val c).property a (hWB ha.1)).self_of_nhds.continuousAt
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
  refine ⟨Φ,hsrc,h0Φ,hflat,U,hU,hmeet,(fun a ha => hpoint a (hWB ha.1)),?_⟩
  dsimp only
  intro a ha
  have hvalue : (ρ a ha.1) b = coefficientGermHom d B a (hWB ha.1) (C0.val c) := by
    rw [← hcb]
    exact congrArg (fun f : C0 →ₐ[ℂ] HolGerm (ComplexModel d) => f c) (hρ a ha.1)
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
        (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a)))) := hp
  exact Module.Free.of_equiv (originalNormalAssociatedGradedQuotientEquiv d t _)


/-- The SAME actual real open gives ALL original nearby canonical centre degrees finite/free/flat and the whole associated module free/flat. -/
theorem exists_original_regular_real_all_degree_canonical_centre_free_open
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel d), IsOpen U ∧
        (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
        (∀ a ∈ U, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        ∀ a ∈ U,
        let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))
        letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
          (originalNormalAssociatedGraded d t Ia) := (originalNormalAssociatedGradedCentreModule d t Ia).toSMul
        letI := originalNormalAssociatedGradedCentreModule d t Ia
        (Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalAssociatedGraded d t Ia) ∧
          Module.Flat (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalAssociatedGraded d t Ia)) ∧
        ∀ q : ℕ,
          letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
            (originalNormalGradedPiece d t Ia q) := (originalNormalGradedPieceCentreModule d t Ia q).toSMul
          letI := originalNormalGradedPieceCentreModule d t Ia q
          Module.Finite (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t Ia q) ∧
          Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t Ia q) ∧
          Module.Flat (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t Ia q) := by
  let := tangentAlgebra d t
  obtain ⟨Φ,hsrc,h0,hflat,U,hU,hmeet,hpoint,hwhole⟩ :=
    exists_original_regular_real_nearby_associated_free_open C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  refine ⟨Φ,hsrc,h0,hflat,U,hU,hmeet,hpoint,?_⟩
  dsimp only
  intro a ha
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))
  have hb : Module.Free (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t Ia) := hwhole a ha
  refine ⟨originalNormalAssociatedGradedCentre_free_flat_of_tangent_free d t Ia hb, ?_⟩
  intro q
  obtain ⟨hfree, hfinite⟩ := all_originalNormalGradedPiece_finite_free_of_associated_free d t Ia hb q
  exact ⟨originalNormalGradedPieceCentre_finite_of_tangent_finite d t q Ia hfinite,
    originalNormalGradedPieceCentre_free_flat_of_tangent_free d t q Ia hfree⟩


end Original

end
end Hironaka.HironakaSmoothCentreRealDomainNearbyFreeness
