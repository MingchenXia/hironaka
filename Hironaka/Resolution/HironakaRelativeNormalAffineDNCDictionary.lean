/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalNearbyPolynomialCoefficientGerms
import Hironaka.Invariant.MonomialPartEtale
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeRestriction
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! Complete prior mathematical route: true functions/whole actual pullback,
original equation and all-colon/central dictionaries, then entire nearby
ORIGINAL initial ideal. No arbitrary origin-germ-to-nearby-germ map. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalAffineDNCDictionary
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalDeformationFiniteRelationsSpread HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaRelativeNormalHomogeneousAnalyticContraction HironakaRelativeNormalGraphCentralIdealEquality
  HironakaHolomorphicJetChartInvariance MonomialPartEtale DerivativeIdealAlongEtale
  RelativePrincipalizationSpan RestrictedIdealExtension
  HironakaSmoothSubmersionRelativeRestriction HironakaSmoothSubmersionOrderedChoiceImageTrace
  FiniteGermIdealPullbackGenerators InvertibleIdealQuotient
attribute [local instance] MvPolynomial.gradedAlgebra


theorem actualAffineTranslation_inverse_left (n : ℕ) (a z : ComplexModel n) :
    actualAffineTranslation n (-a) (actualAffineTranslation n a z) = z := by
  simp only [actualAffineTranslation,neg_add_cancel_left]

theorem actualAffineTranslation_inverse_right (n : ℕ) (a z : ComplexModel n) :
    actualAffineTranslation n a (actualAffineTranslation n (-a) z) = z := by
  simp only [actualAffineTranslation,add_neg_cancel_left]

theorem actualAffineTranslation_localInverse (n : ℕ) (a y : ComplexModel n) :
    IsLocalInverseAt n (actualAffineTranslation n a) (actualAffineTranslation n (-a)) y := by
  refine ⟨?_,?_,Eventually.of_forall (actualAffineTranslation_inverse_left n a),
    Eventually.of_forall (actualAffineTranslation_inverse_right n a)⟩
  · exact Eventually.of_forall fun z => (actualAffineTranslation_contMDiff n a z).mdifferentiableAt (by simp)
  · exact Eventually.of_forall fun z => (actualAffineTranslation_contMDiff n (-a) z).mdifferentiableAt (by simp)

theorem actualAffineTranslation_whole_membership (n : ℕ) (a y : ComplexModel n)
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) (f : ComplexModel n → ℂ) :
    (actualTranslatedOriginalSheaf I a).mem y f ↔
      I.mem (actualAffineTranslation n a y) (f ∘ actualAffineTranslation n (-a)) :=
  mem_pullback_iff_of_local hI (actualAffineTranslation_localInverse n a y)

private theorem actual_affine_composition_holomorphic (n : ℕ) (a y : ComplexModel n)
    (f : ComplexModel n → ℂ) (hf : HolAt f (actualAffineTranslation n a y)) :
    HolAt (f ∘ actualAffineTranslation n a) y := by
  have ht : Tendsto (actualAffineTranslation n a) (𝓝 y) (𝓝 (actualAffineTranslation n a y)) :=
    (actualAffineTranslation_contMDiff n a).continuous.tendsto y
  exact (ht.eventually hf).mono fun z hz =>
    hz.comp z ((differentiableAt_const a).add differentiableAt_id)

theorem actualAffineTranslation_whole_holomorphic (n : ℕ) (a y : ComplexModel n)
    (f : ComplexModel n → ℂ) :
    HolAt f y ↔ HolAt (f ∘ actualAffineTranslation n (-a)) (actualAffineTranslation n a y) := by
  constructor
  · intro hf
    apply actual_affine_composition_holomorphic
    simpa only [actualAffineTranslation_inverse_left] using hf
  · intro hf
    have hh := actual_affine_composition_holomorphic n a y
      (f ∘ actualAffineTranslation n (-a)) hf
    have he : (f ∘ actualAffineTranslation n (-a)) ∘ actualAffineTranslation n a = f :=
      funext fun z => congrArg f (actualAffineTranslation_inverse_left n a z)
    rwa [he] at hh

def actualDNCBaseShift (d t : ℕ) (a : ComplexModel d) :
    ComplexModel (deformationDimension d t) → ComplexModel (deformationDimension d t) :=
  actualAffineTranslation (deformationDimension d t)
    (deformationCentralInclusion d t (tangentInclusion d t a))

theorem actualDNCBaseShift_holomorphic (d t : ℕ) (a : ComplexModel d) :
    ContMDiff 𝓘(ℂ,ComplexModel (deformationDimension d t))
      𝓘(ℂ,ComplexModel (deformationDimension d t)) ∞ (actualDNCBaseShift d t a) :=
  actualAffineTranslation_contMDiff _ _

private theorem actual_projection_basepoint (d t : ℕ) (a : ComplexModel d) :
    deformationProjection d t (deformationCentralInclusion d t (tangentInclusion d t a)) =
      tangentInclusion d t a := by
  ext i
  change deformationCentralInclusion d t (tangentInclusion d t a) (i.castAdd (1+t)) = tangentInclusion d t a i
  by_cases hi : i.val < d
  · let j : Fin d := ⟨i.val,hi⟩
    have he : i = j.castAdd t := Fin.ext rfl
    rw [he,deformationCentralInclusion_tangent]
  · let j : Fin t := ⟨i.val-d,by have h:=i.isLt;omega⟩
    have he : i = j.natAdd d := Fin.ext (by dsimp only [j];change i.val = d+(i.val-d);omega)
    rw [he,deformationCentralInclusion_normal,tangentInclusion_normal]

theorem actualDNCBaseShift_projection (d t : ℕ) (a : ComplexModel d)
    (z : ComplexModel (deformationDimension d t)) :
    deformationProjection d t (actualDNCBaseShift d t a z) =
      actualAffineTranslation (d+t) (tangentInclusion d t a) (deformationProjection d t z) := by
  change deformationProjection d t (deformationCentralInclusion d t (tangentInclusion d t a)+z) = _
  rw [map_add,actual_projection_basepoint]
  rfl

theorem actualDNCBaseShift_parameter (d t : ℕ) (a : ComplexModel d)
    (z : ComplexModel (deformationDimension d t)) :
    deformationParameter d t (actualDNCBaseShift d t a z) = deformationParameter d t z := by
  change deformationParameter d t (deformationCentralInclusion d t (tangentInclusion d t a)+z) = _
  rw [map_add,deformationCentralInclusion_parameter,zero_add]

theorem actualDNCBaseShift_fiber (d t : ℕ) (a : ComplexModel d)
    (z : ComplexModel (deformationDimension d t)) (i : Fin t) :
    deformationFiberCoordinate d t i (actualDNCBaseShift d t a z) = deformationFiberCoordinate d t i z := by
  change deformationFiberCoordinate d t i (deformationCentralInclusion d t (tangentInclusion d t a)+z) = _
  rw [map_add,deformationCentralInclusion_fiber,tangentInclusion_normal,zero_add]

theorem actualDNCBaseShift_original_normal (d t : ℕ) (a : ComplexModel d)
    (z : ComplexModel (deformationDimension d t)) (i : Fin t) :
    actualDNCBaseShift d t a z ((i.natAdd d).castAdd (1+t)) = z ((i.natAdd d).castAdd (1+t)) := by
  change (deformationCentralInclusion d t (tangentInclusion d t a)+z) ((i.natAdd d).castAdd (1+t)) = _
  rw [PiLp.add_apply,deformationCentralInclusion_normal,zero_add]

theorem actualDNCBaseShift_equation (d t : ℕ) (a : ComplexModel d)
    (z : ComplexModel (deformationDimension d t)) (i : Fin t) :
    deformationEquation d t i (actualDNCBaseShift d t a z) = deformationEquation d t i z := by
  simp only [deformationEquation,actualDNCBaseShift_parameter,actualDNCBaseShift_fiber,actualDNCBaseShift_original_normal]

theorem actualDNCBaseShift_central (d t : ℕ) (a : ComplexModel d)
    (z : ComplexModel (d+t)) :
    deformationCentralInclusion d t (actualAffineTranslation (d+t) (tangentInclusion d t a) z) =
      actualDNCBaseShift d t a (deformationCentralInclusion d t z) :=
  map_add (deformationCentralInclusion d t) _ _


theorem actualDNCBaseShift_equationIdeal (d t : ℕ) (a : ComplexModel d) :
    GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
      (deformationEquationIdeal d t) = deformationEquationIdeal d t := by
  apply GermIdeal.ext
  funext y f
  apply propext
  have hgen := mem_pullback_iff_of_finite_generation (y := y)
    (Eventually.of_forall fun _ => (actualDNCBaseShift_holomorphic d t a).contMDiffAt)
    (deformationEquationIdeal d t) (deformationEquation d t)
    (fun i => Eventually.of_forall fun z =>
      (deformationEquation_holomorphic d t i z).mdifferentiableAt)
    (fun _ => Iff.rfl) f
  have he : (fun i => deformationEquation d t i ∘ actualDNCBaseShift d t a) = deformationEquation d t := by
    funext i z
    exact actualDNCBaseShift_equation d t a z i
  rw [he] at hgen
  exact hgen

theorem actual_original_deformation_translation (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) (a : ComplexModel d) :
    originalDeformationIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) =
      GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
        (originalDeformationIdeal d t I) := by
  unfold originalDeformationIdeal
  rw [pullback_sumIdeal_dimensions (actualDNCBaseShift_holomorphic d t a)
    (GermIdealPullbackCalculus.isCoherent_pullback (deformationProjection d t).contMDiff hI)
    (deformationEquationIdeal_isCoherent d t),actualDNCBaseShift_equationIdeal]
  congr 1
  change GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t)
    (GermIdeal.pullback (m := d+t) (actualAffineTranslation (d+t) (tangentInclusion d t a)) I) = _
  rw [← coherent_pullback_comp (actualAffineTranslation_contMDiff (d+t) (tangentInclusion d t a))
      (deformationProjection d t).contMDiff I hI,
    ← coherent_pullback_comp (deformationProjection d t).contMDiff
      (actualDNCBaseShift_holomorphic d t a) I hI]
  congr 1
  funext z
  exact (actualDNCBaseShift_projection d t a z).symm

theorem actualAffineTranslation_whole_colon (n : ℕ) (a : ComplexModel n)
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent)
    (h : ComplexModel n → ℂ) (hh : ∀ x, HolAt h x)
    (hinv : ∀ z, h (actualAffineTranslation n (-a) z) = h z) (q : ℕ) :
    actualColonGermIdeal (actualTranslatedOriginalSheaf I a) h q =
      actualTranslatedOriginalSheaf (actualColonGermIdeal I h q) a := by
  induction q with
  | zero => rfl
  | succ q ih =>
    apply GermIdeal.ext
    funext y f
    apply propext
    change (HolAt f y ∧ (actualColonGermIdeal (actualTranslatedOriginalSheaf I a) h q).mem y
      (fun z => f z*h z)) ↔ (actualTranslatedOriginalSheaf (actualColonGermIdeal I h (q+1)) a).mem y f
    rw [ih,actualAffineTranslation_whole_membership n a y _ (actualColonGermIdeal_isCoherent I hI h hh q),
      actualAffineTranslation_whole_membership n a y _ (actualColonGermIdeal_isCoherent I hI h hh (q+1))]
    change (HolAt f y ∧ actualColonChain I.mem h q (actualAffineTranslation n a y)
      ((fun z => f z*h z) ∘ actualAffineTranslation n (-a))) ↔
      (HolAt (f ∘ actualAffineTranslation n (-a)) (actualAffineTranslation n a y) ∧
        actualColonChain I.mem h q (actualAffineTranslation n a y)
          (fun z => (f ∘ actualAffineTranslation n (-a)) z*h z))
    rw [actualAffineTranslation_whole_holomorphic n a y f]
    have he : (fun z => f z*h z) ∘ actualAffineTranslation n (-a) =
        fun z => (f ∘ actualAffineTranslation n (-a)) z*h z := by
      funext z
      simp only [Function.comp_apply,hinv]
    rw [he]

theorem actual_original_colon_translation (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent)
    (a : ComplexModel d) (q : ℕ) :
    originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) q =
      GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
        (originalDeformationColonIdeal d t I q) := by
  unfold originalDeformationColonIdeal
  rw [actual_original_deformation_translation d t I hI a]
  apply actualAffineTranslation_whole_colon
  · exact originalDeformationIdeal_isCoherent d t I hI
  · exact fun _ => Eventually.of_forall fun z => (deformationParameter d t).differentiableAt
  · intro z
    change deformationParameter d t
      (-deformationCentralInclusion d t (tangentInclusion d t a)+z) = _
    rw [map_add,map_neg,deformationCentralInclusion_parameter,neg_zero,zero_add]

theorem actual_original_central_translation (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent)
    (a : ComplexModel d) (q : ℕ) :
    originalDeformationCentralIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) q =
      actualTranslatedOriginalSheaf (originalDeformationCentralIdeal d t I q) (tangentInclusion d t a) := by
  unfold originalDeformationCentralIdeal
  rw [actual_original_colon_translation d t I hI a]
  change GermIdeal.pullback (m := d+t) (deformationCentralInclusion d t)
    (GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
      (originalDeformationColonIdeal d t I q)) =
    GermIdeal.pullback (m := d+t) (actualAffineTranslation (d+t) (tangentInclusion d t a))
      (GermIdeal.pullback (m := d+t) (deformationCentralInclusion d t)
        (originalDeformationColonIdeal d t I q))
  rw [← coherent_pullback_comp (actualDNCBaseShift_holomorphic d t a)
      (deformationCentralInclusion d t).contMDiff _ (originalDeformationColonIdeal_isCoherent d t I hI q),
    ← coherent_pullback_comp (deformationCentralInclusion d t).contMDiff
      (actualAffineTranslation_contMDiff (d+t) (tangentInclusion d t a)) _
        (originalDeformationColonIdeal_isCoherent d t I hI q)]
  congr 1
  funext z
  exact (actualDNCBaseShift_central d t a z).symm


private theorem actual_original_colon_origin_dictionary (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent)
    (a : ComplexModel d) (q : ℕ) (f : ComplexModel (deformationDimension d t) → ℂ) :
    (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) q).mem 0 f ↔
      (originalDeformationColonIdeal d t I q).mem
        (deformationCentralInclusion d t (tangentInclusion d t a))
        (f ∘ actualAffineTranslation (deformationDimension d t)
          (-deformationCentralInclusion d t (tangentInclusion d t a))) := by
  rw [actual_original_colon_translation d t I hI a q]
  change (actualTranslatedOriginalSheaf (originalDeformationColonIdeal d t I q)
    (deformationCentralInclusion d t (tangentInclusion d t a))).mem 0 f ↔ _
  simpa only [actualAffineTranslation_zero] using
    actualAffineTranslation_whole_membership (deformationDimension d t)
      (deformationCentralInclusion d t (tangentInclusion d t a)) 0
      (originalDeformationColonIdeal d t I q) (originalDeformationColonIdeal_isCoherent d t I hI q) f

theorem actual_original_translated_stabilization (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent)
    (a : ComplexModel d) (N : ℕ)
    (hN : ∀ q : ℕ, ∀ g,
      (originalDeformationColonIdeal d t I (N+q)).mem
        (deformationCentralInclusion d t (tangentInclusion d t a)) g ↔
      (originalDeformationColonIdeal d t I N).mem
        (deformationCentralInclusion d t (tangentInclusion d t a)) g) :
    ∀ q : ℕ, ∀ f,
      (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) (N+q)).mem 0 f ↔
        (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) N).mem 0 f := by
  intro q f
  rw [actual_original_colon_origin_dictionary d t I hI a (N+q) f,
    actual_original_colon_origin_dictionary d t I hI a N f]
  exact hN q _

private theorem actual_central_origin_eq_of_colon_origin (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (N L : ℕ)
    (hNL : ∀ f, (originalDeformationColonIdeal d t I N).mem 0 f ↔
      (originalDeformationColonIdeal d t I L).mem 0 f) :
    originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) =
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I L) := by
  have hcentral : ∀ f, (originalDeformationCentralIdeal d t I N).mem 0 f ↔
      (originalDeformationCentralIdeal d t I L).mem 0 f := by
    intro f
    constructor
    · intro hf
      apply GermIdeal.mem_pullback_iff.mpr
      apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hf)
      rintro _ ⟨g,hg,rfl⟩
      exact ⟨g,by simpa only [map_zero] using (hNL g).mp (by simpa only [map_zero] using hg),rfl⟩
    · intro hf
      apply GermIdeal.mem_pullback_iff.mpr
      apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hf)
      rintro _ ⟨g,hg,rfl⟩
      exact ⟨g,by simpa only [map_zero] using (hNL g).mpr (by simpa only [map_zero] using hg),rfl⟩
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨f,hf,hIf,rfl⟩
    exact ⟨f,hf,(hcentral f).mp hIf,rfl⟩
  · rintro ⟨f,hf,hIf,rfl⟩
    exact ⟨f,hf,(hcentral f).mpr hIf,rfl⟩

theorem whole_central_origin_same_stable_index (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (N L : ℕ)
    (hN : ∀ q : ℕ, ∀ f, (originalDeformationColonIdeal d t I (N+q)).mem 0 f ↔
      (originalDeformationColonIdeal d t I N).mem 0 f)
    (hL : ∀ q : ℕ, ∀ f, (originalDeformationColonIdeal d t I (L+q)).mem 0 f ↔
      (originalDeformationColonIdeal d t I L).mem 0 f) :
    originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) =
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I L) := by
  apply actual_central_origin_eq_of_colon_origin d t I N L
  intro f
  by_cases hNL : N ≤ L
  · have hs := hN (L-N) f
    have he : N+(L-N) = L := by omega
    rw [he] at hs
    exact hs.symm
  · have hs := hL (N-L) f
    have he : L+(N-L) = N := by omega
    rw [he] at hs
    exact hs

theorem exists_original_whole_nearby_normal_initial_ideal (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ N : ℕ, ∃ B : Set (ComplexModel d), IsOpen B ∧ 0 ∈ B ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ a ∈ B, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem (deformationCentralInclusion d t (tangentInclusion d t a)) g ↔
          (originalDeformationColonIdeal d t I N).mem (deformationCentralInclusion d t (tangentInclusion d t a)) g) ∧
      ∃ hc : ∀ a ∈ B, ∀ P : ↥(actualOriginalRelationFamily d t I), ∀ α,
        HolAt (actualCoefficientRepresentative (P.val.coeff α)) a,
        ∀ a (ha : a ∈ B),
          let J := actualTranslatedOriginalSheaf I (tangentInclusion d t a)
          let H := Ideal.span (range fun P : ↥(actualOriginalRelationFamily d t I) =>
            actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
          J.IsCoherent ∧
          H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) ∧
          H = originalNormalInitialIdeal d t (originalCoherentOriginIdeal J) ∧
          Nonempty ((MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ H)
            ≃ₗ[HolGerm (ComplexModel d)] originalNormalAssociatedGraded d t (originalCoherentOriginIdeal J)) ∧
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
            originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
              (originalDeformationCentralIdeal d t I N) (tangentInclusion d t a)) ∧
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
            Ideal.map (normalPolynomialEval d t).toRingHom H ∧
          (∀ q : ℕ, ∀ f, (originalDeformationColonIdeal d t J (N+q)).mem 0 f ↔
            (originalDeformationColonIdeal d t J N).mem 0 f) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨N,B,hB,h0B,hcent,hchain,hc,hmodels⟩ :=
    exists_original_whole_translated_central_polynomial_model d t I hI
  refine ⟨N,B,hB,h0B,hcent,hchain,hc,?_⟩
  intro a ha
  dsimp only
  let J := actualTranslatedOriginalSheaf I (tangentInclusion d t a)
  let H := Ideal.span (range fun P : ↥(actualOriginalRelationFamily d t I) =>
    actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
  have hJ : J.IsCoherent := actualTranslatedOriginalSheaf_isCoherent I hI (tangentInclusion d t a)
  obtain ⟨hH,hmodel,_hcomap⟩ := hmodels a ha
  have hN := actual_original_translated_stabilization d t I hI a N (hchain a ha)
  have hcentral := actual_original_central_translation d t I hI a N
  obtain ⟨L,U,_hU,h0U,_hcol,_hcent,hLchain,_hpow,_hsat,hkernel⟩ :=
    exists_original_coherent_whole_central_polynomial_kernel d t J hJ
  have hsame := whole_central_origin_same_stable_index d t J N L hN (hLchain 0 h0U)
  have hmodelJ : originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
      Ideal.map (normalPolynomialEval d t).toRingHom H := by
    rw [hcentral]
    exact hmodel
  have hHK : H = originalNormalInitialIdeal d t (originalCoherentOriginIdeal J) := by
    ext P
    calc
      P ∈ H ↔ normalPolynomialEval d t P ∈ Ideal.map (normalPolynomialEval d t).toRingHom H :=
        (normalPolynomialEval_mem_analytic_map_iff d t H hH P).symm
      _ ↔ normalPolynomialEval d t P ∈ originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) :=
        by rw [hmodelJ]
      _ ↔ normalPolynomialEval d t P ∈ originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J L) :=
        by rw [hsame]
      _ ↔ P ∈ originalNormalInitialIdeal d t (originalCoherentOriginIdeal J) := hkernel P
  have hwholeModule : Nonempty ((MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ H)
      ≃ₗ[HolGerm (ComplexModel d)] originalNormalAssociatedGraded d t (originalCoherentOriginIdeal J)) := by
    exact ⟨(Submodule.quotEquivOfEq _ _ (congrArg
      (fun K : Ideal (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) =>
        K.restrictScalars (HolGerm (ComplexModel d))) hHK)).trans
          (originalNormalAssociatedGradedQuotientEquiv d t (originalCoherentOriginIdeal J))⟩
  exact ⟨hJ,hH,hHK,hwholeModule,congrArg originalCoherentOriginIdeal hcentral,hmodelJ,hN⟩

end
end Hironaka.HironakaRelativeNormalAffineDNCDictionary
