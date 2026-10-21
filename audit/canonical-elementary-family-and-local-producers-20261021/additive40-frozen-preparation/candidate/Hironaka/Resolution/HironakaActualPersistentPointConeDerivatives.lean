/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointNormalizedBennett
import Hironaka.Resolution.HironakaActualSuppliedFlatteningNormalPowers
import Mathlib.RingTheory.MvPowerSeries.Rename

/-! Genuine source-cone derivative stability from actual zero-direction point HS persistence. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPersistentPointConeDerivatives
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalMonomialBasis
  HironakaActualFormalInitialDiagram HironakaActualHomogeneousInitialHS
  HironakaActualFiniteInitialGeneration HironakaActualTranslatedInitialHS
  HironakaActualPointNormalizedBennett HironakaActualPointInitialIdealInclusion
  HironakaActualUnshiftedInitialHSTransfer HironakaActualPointUnitCoordinateChange
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticStrictGenerators
  HironakaActualSuppliedFlatteningNormalPowers HironakaActualHSConstantCentreJetFrames
  HironakaActualCentreCoupledSymbols HironakaRelativeNormalIdeal
  HironakaActualHomogeneousInitialTangentDerivatives HironakaActualOriginalFormalTaylor
  HironakaActualOriginalFormalHSTransfer HironakaSmoothCentreRealDomainActualAmbientHS
variable {n : ℕ}

private theorem polynomial_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : MvPolynomial (Fin n) ℂ) (x : Fin n → E → ℂ) (hx : ∀ i, ContDiff ℂ ∞ (x i)) :
    ContDiff ℂ ∞ (fun z => MvPolynomial.eval (fun i => x i z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const : ContDiff ℂ ∞ (fun _ : E => c))
  | add P Q hP hQ => simpa only [MvPolynomial.eval_add] using hP.add hQ
  | mul_X P i hP => simpa only [MvPolynomial.eval_mul,MvPolynomial.eval_X] using hP.mul (hx i)

private def polyFunction (P : MvPolynomial (Fin n) ℂ) (z : ComplexModel n) : ℂ :=
  MvPolynomial.eval (fun i => z i) P

private theorem polyFunction_contDiff (P : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ ∞ (polyFunction P) :=
  polynomial_contDiff (E := ComplexModel n) P (fun i z => z i)
    (fun i => (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff)

private theorem polyFunction_hol (P : MvPolynomial (Fin n) ℂ) (p : ComplexModel n) :
    HolAt (polyFunction P) p :=
  Eventually.of_forall fun _ => ((polyFunction_contDiff P).differentiable (by simp)).differentiableAt

private theorem translated_poly_mk (p : ComplexModel n) (P : MvPolynomial (Fin n) ℂ) :
    actualUnshiftedTranslatedPolynomialEval n (fun i => p i) P =
      translatedGerm p (polyFunction P) (polyFunction_hol P p) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [actualUnshiftedTranslatedPolynomialEval,MvPolynomial.aeval_C,translatedGerm,polyFunction,MvPolynomial.eval_C]
    rfl
  | add P Q hP hQ =>
    rw [map_add,hP,hQ]
    unfold translatedGerm
    rw [← HolGerm.mk_add]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => MvPolynomial.eval_add.symm
  | mul_X P i hP =>
    rw [map_mul,hP,actualUnshiftedTranslatedPolynomialEval,MvPolynomial.aeval_X]
    unfold translatedGerm
    change HolGerm.mk (fun z => polyFunction P (z+p)) _ *
      (coordinateGerm i+algebraMap ℂ _ (p i)) = _
    change HolGerm.mk (fun z => polyFunction P (z+p)) _ *
      (HolGerm.mk (fun z => z i) _+HolGerm.mk (fun _ => p i) (eventually_differentiableAt_const (p i))) = _
    rw [← HolGerm.mk_add,← HolGerm.mk_mul]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [polyFunction,MvPolynomial.eval_mul,MvPolynomial.eval_X]

private def coneFunctions (K : Ideal (MvPowerSeries (Fin n) ℂ)) :=
  fun a : actualInitialVertices MonomialOrder.degLex K => polyFunction (actualInitialVertexPolynomial K a)

def coneSheaf (K : Ideal (MvPowerSeries (Fin n) ℂ)) : GermIdeal n (ComplexModel n) where
  mem p f := IsInSpanAt (n := n) (· ∈ range (coneFunctions K)) p f

theorem coneSheaf_isCoherent (K : Ideal (MvPowerSeries (Fin n) ℂ)) : (coneSheaf K).IsCoherent := by
  let v := (Fintype.equivFin (actualInitialVertices MonomialOrder.degLex K)).symm
  intro x
  refine ⟨univ,isOpen_univ,mem_univ _,_,fun i => coneFunctions K (v i),?_,?_⟩
  · intro i
    exact ((polyFunction_contDiff (actualInitialVertexPolynomial K (v i))).contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  · intro y _ f
    change IsInSpanAt (n := n) (· ∈ range (coneFunctions K)) y f ↔ _
    have he : range (fun i => coneFunctions K (v i))=range (coneFunctions K) :=
      by ext f; constructor
         · rintro ⟨i,rfl⟩; exact ⟨v i,rfl⟩
         · rintro ⟨a,rfl⟩; obtain ⟨i,rfl⟩ := v.surjective a; exact ⟨i,rfl⟩
    rw [he]

theorem coneTranslatedIdeal_eq (K : Ideal (MvPowerSeries (Fin n) ℂ)) (p : ComplexModel n) :
    translatedIdeal (coneFunctions K) p (fun _ => polyFunction_hol _ p)=
      actualUnshiftedTranslatedInitialIdeal K (fun i => p i) := by
  unfold translatedIdeal actualUnshiftedTranslatedInitialIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact (translated_poly_mk p _).symm

theorem cone_origin_formal (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (actualUnshiftedTranslatedInitialIdeal K 0)=actualHomogeneousInitialIdeal K := by
  rw [actualUnshiftedTranslatedInitialIdeal_formal_extension,actualTranslatedInitialFormalIdeal]
  rw [actualHomogeneousInitialIdeal_eq_initial_vertex_span]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  change MvPolynomial.aeval (fun i => MvPowerSeries.X i+algebraMap ℂ _ (0 : ℂ))
      (actualInitialVertexPolynomial K a)=_
  simp only [map_zero,add_zero]
  have he : (MvPolynomial.aeval (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ))=
      (MvPolynomial.coeToMvPowerSeries.algHom ℂ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [he]
  exact actualInitialVertexPolynomial_coe K a

theorem translated_cone_hs_eq_of_zero_point_persistence
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n)
    (hPersist : ∀ ℓ, hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal I univ e (fun _ => 0)) ℓ=hilbertSamuelValue I ℓ)
    (c : ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)
      (fun i => c*(if i=e then 1 else 0))) ℓ=hilbertSamuelValue I ℓ := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  let p : Fin n → ℂ := fun i => if i=e then 1 else 0
  have hp : (actualPointUnitBasePoint e (fun _ => 0)).ofLp=p := by
    funext i
    simp only [actualPointUnitBasePoint_apply,p]
  have hunit : hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal K p) ℓ=
      hilbertSamuelValue I ℓ := by
    apply le_antisymm (hilbertSamuelValue_actual_original_translated_initial_le n I p ℓ)
    rw [← hPersist ℓ]
    have hb := hilbertSamuelValue_actual_point_normalized_le_dehomogenized_initial n I e (fun _ => 0) ℓ
    rw [hilbertSamuelValue_actualDehomogenizedInitialIdeal_eq_translated,hp] at hb
    exact hb
  by_cases hc : c=0
  · subst c
    have he : (fun i => (0 : ℂ)*(if i=e then 1 else 0))=(0 : Fin n → ℂ) := by funext i; simp
    rw [he,hilbertSamuelValue_eq_actual_unshifted_formal_extension,
      actualUnshiftedTranslatedInitialIdeal_formal_extension]
    have h0 := cone_origin_formal K
    rw [actualUnshiftedTranslatedInitialIdeal_formal_extension] at h0
    rw [h0,← genuineFormalHilbertSamuelValue_homogeneous_initial,
      ← hilbertSamuelValue_eq_actual_unshifted_formal_extension n I]
  · have hformal := actualTranslatedInitialIdeal_nonzero_ray_hs K p c hc ℓ
    rw [hilbertSamuelValue_eq_genuine_formal_extension,
      hilbertSamuelValue_eq_genuine_formal_extension,
      actualTranslatedInitialIdeal_formal_extension,
      actualTranslatedInitialIdeal_formal_extension] at hformal
    rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,
      actualUnshiftedTranslatedInitialIdeal_formal_extension,
      show (fun i => c*(if i=e then 1 else 0))=c • p from rfl,
      hformal,← actualUnshiftedTranslatedInitialIdeal_formal_extension,
      ← hilbertSamuelValue_eq_actual_unshifted_formal_extension]
    exact hunit

private theorem polynomial_coe_homogeneous (P : MvPolynomial (Fin n) ℂ) (d : ℕ)
    (hP : P.IsHomogeneous d) : (P : MvPowerSeries (Fin n) ℂ).IsHomogeneous d := by
  intro a ha
  apply hP
  simpa only [MvPolynomial.coeff_coe] using ha

private theorem homogeneous_span_initial_eq {ι : Type*}
    (P : ι → MvPolynomial (Fin n) ℂ) (d : ι → ℕ) (hP : ∀ i,(P i).IsHomogeneous (d i)) :
    actualHomogeneousInitialIdeal (Ideal.span (range fun i => (P i : MvPowerSeries (Fin n) ℂ)))=
      Ideal.span (range fun i => (P i : MvPowerSeries (Fin n) ℂ)) := by
  let J : Ideal (MvPowerSeries (Fin n) ℂ) := Ideal.span (range fun i => (P i : MvPowerSeries (Fin n) ℂ))
  have hcomponent (F : MvPowerSeries (Fin n) ℂ) (hF : F∈J) (q : ℕ) :
      MvPowerSeries.homogeneousComponent q F∈J := by
    obtain ⟨c,hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hF
    rw [←hc]
    change MvPowerSeries.homogeneousComponent q (∑ i∈c.support,c i*(P i : MvPowerSeries (Fin n) ℂ))∈J
    rw [map_sum]
    apply Ideal.sum_mem
    intro i _
    by_cases hi : d i≤q
    · rw [homogeneousComponent_mul_homogeneous_of_le q (d i) _ _ (polynomial_coe_homogeneous _ _ (hP i)) hi]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
    · rw [homogeneousComponent_mul_homogeneous_of_lt q (d i) _ _ (polynomial_coe_homogeneous _ _ (hP i)) (lt_of_not_ge hi)]
      exact Ideal.zero_mem _
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨F,rfl⟩
    exact hcomponent F.val F.property.1 _
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change (P i : MvPowerSeries (Fin n) ℂ)∈_
    by_cases hz : (P i : MvPowerSeries (Fin n) ℂ)=0
    · rw [hz]; exact Ideal.zero_mem _
    have hh : (P i : MvPowerSeries (Fin n) ℂ).IsHomogeneous (d i) :=
      polynomial_coe_homogeneous (P i) (d i) (hP i)
    have hd : actualHomogeneousInitialDegree (P i : MvPowerSeries (Fin n) ℂ) hz=d i := by
      have hc := hh ((actualInitialExponent_spec MonomialOrder.degLex (P i : MvPowerSeries (Fin n) ℂ) hz).1)
      simpa [actualHomogeneousInitialDegree,normalExponentDegree,Finsupp.degree_eq_sum,Finsupp.weight_eq_sum] using hc
    have hf : actualHomogeneousInitialForm (P i : MvPowerSeries (Fin n) ℂ) hz=(P i : MvPowerSeries (Fin n) ℂ) := by
      rw [actualHomogeneousInitialForm,hd]
      exact (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hh).symm
    rw [←hf]
    exact Ideal.subset_span ⟨⟨_,Ideal.subset_span ⟨i,rfl⟩,hz⟩,rfl⟩
private def permLinear (r : Fin n ≃ Fin n) : ComplexModel n ≃L[ℂ] ComplexModel n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ r.symm).toContinuousLinearEquiv

private def permGerm (r : Fin n ≃ Fin n) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) where
  toRingEquiv := HolGerm.comapEquiv (permLinear r)
  commutes' _ := rfl

private theorem permGerm_coordinate (r : Fin n ≃ Fin n) (i : Fin n) :
    permGerm r (coordinateGerm i)=coordinateGerm (r i) := by
  change HolGerm.comapEquiv (permLinear r) (HolGerm.mk (fun z : ComplexModel n => z i) _)=
    HolGerm.mk (fun z : ComplexModel n => z (r i)) _
  rw [HolGerm.comapEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => rfl

private theorem permGerm_polynomial (r : Fin n ≃ Fin n) (p : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    permGerm r (actualUnshiftedTranslatedPolynomialEval n (fun i => p (r i)) P)=
      actualUnshiftedTranslatedPolynomialEval n p (MvPolynomial.rename r P) := by
  have he : (permGerm r).toAlgHom.comp
      (actualUnshiftedTranslatedPolynomialEval n (fun i => p (r i)))=
      (actualUnshiftedTranslatedPolynomialEval n p).comp (MvPolynomial.rename r) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,actualUnshiftedTranslatedPolynomialEval,MvPolynomial.aeval_X,
      MvPolynomial.rename_X]
    change permGerm r (coordinateGerm i+algebraMap ℂ _ (p (r i)))=_
    rw [map_add,permGerm_coordinate,AlgEquiv.commutes]
  exact DFunLike.congr_fun he P

private def polyTranslatedIdeal {ι : Type*} (P : ι → MvPolynomial (Fin n) ℂ) (p : Fin n → ℂ) :
    Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span (range fun i => actualUnshiftedTranslatedPolynomialEval n p (P i))

private theorem map_perm_polyTranslatedIdeal {ι : Type*} (r : Fin n ≃ Fin n)
    (P : ι → MvPolynomial (Fin n) ℂ) (p : Fin n → ℂ) :
    Ideal.map (permGerm r).toRingEquiv.toRingHom (polyTranslatedIdeal P (fun i => p (r i)))=
      polyTranslatedIdeal (fun i => MvPolynomial.rename r (P i)) p := by
  rw [polyTranslatedIdeal,polyTranslatedIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact permGerm_polynomial r p (P i)

private theorem translated_polyIdeal_eq {ι : Type*} (P : ι → MvPolynomial (Fin n) ℂ)
    (p : ComplexModel n) :
    translatedIdeal (fun i => polyFunction (P i)) p (fun i => polyFunction_hol (P i) p)=
      polyTranslatedIdeal P (fun i => p i) := by
  unfold translatedIdeal polyTranslatedIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact (translated_poly_mk p (P i)).symm

private theorem polyTranslatedIdeal_origin_formal {ι : Type*} (P : ι → MvPolynomial (Fin n) ℂ) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (polyTranslatedIdeal P 0)=
      Ideal.span (range fun i => (P i : MvPowerSeries (Fin n) ℂ)) := by
  rw [polyTranslatedIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  have he : (actualUnshiftedTaylorAlgHom n).comp (actualUnshiftedTranslatedPolynomialEval n 0)=
      MvPolynomial.coeToMvPowerSeries.algHom ℂ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply,actualUnshiftedTranslatedPolynomialEval,MvPolynomial.aeval_X,
      actualUnshiftedTaylor_coordinate,Pi.zero_apply,map_zero,add_zero]
    simp
  exact DFunLike.congr_fun he (P i)

private theorem homogeneous_polynomial_span_pderiv_of_axis_hs
    {t : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin (1+t)) ℂ) (d : ι → ℕ)
    (hP : ∀ i,(P i).IsHomogeneous (d i))
    (hHS : ∀ p : ComplexModel (1+t), p∈complexCoordinatePlane (1+t) 1 → ∀ ℓ,
      hilbertSamuelValue (polyTranslatedIdeal P (fun i => p i)) ℓ=
        hilbertSamuelValue (polyTranslatedIdeal P 0) ℓ)
    (F : MvPowerSeries (Fin (1+t)) ℂ)
    (hF : F∈Ideal.span (range fun i => (P i : MvPowerSeries (Fin (1+t)) ℂ))) :
    MvPowerSeries.pderiv ℂ 0 F∈Ideal.span (range fun i => (P i : MvPowerSeries (Fin (1+t)) ℂ)) := by
  let G := fun i => polyFunction (P i)
  have hG : ∀ i,DifferentiableOn ℂ (G i) univ :=
    fun i => ((polyFunction_contDiff (P i)).differentiable (by simp)).differentiableOn
  have hr p (_hp : p∈(univ : Set (ComplexModel (1+t))))
      (hplane : p∈complexCoordinatePlane (1+t) 1) (ℓ : ℕ) :
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) G p))=
        Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) G 0)) := by
    apply originalMacaulay_rank_eq_of_translated_hs_eq ℓ G p 0
      (fun i => polyFunction_hol (P i) p) (fun i => polyFunction_hol (P i) 0)
    rw [translated_polyIdeal_eq,translated_polyIdeal_eq]
    exact hHS p hplane ℓ
  obtain ⟨_hf,hD⟩ := actual_family_coupled_normal_data 1 t G univ isOpen_univ (mem_univ _) hG hr
  have hI : Ideal.span (range fun i => HolGerm.mk (G i)
      (HironakaActualHSZeroCentreVanishing.actual_family_holomorphicAt isOpen_univ G hG 0 (mem_univ _) i))=
      polyTranslatedIdeal P 0 := by
    have he := translated_polyIdeal_eq P (0 : ComplexModel (1+t))
    have hzero : (fun i => (0 : ComplexModel (1+t)) i)=(0 : Fin (1+t) → ℂ) := by funext i; rfl
    rw [hzero] at he
    exact (translatedIdeal_zero_eq_span (1+t) G _ _).symm.trans he
  rw [hI,polyTranslatedIdeal_origin_formal,homogeneous_span_initial_eq P d hP] at hD
  exact hD 0 F hF

private theorem map_rename_polynomial_span {ι : Type*} (r : Fin n ≃ Fin n)
    (P : ι → MvPolynomial (Fin n) ℂ) :
    Ideal.map (MvPowerSeries.renameEquiv ℂ r).toRingEquiv.toRingHom
      (Ideal.span (range fun i => (P i : MvPowerSeries (Fin n) ℂ)))=
      Ideal.span (range fun i => (MvPolynomial.rename r (P i) : MvPowerSeries (Fin n) ℂ)) := by
  rw [Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact MvPowerSeries.rename_coe r (P i)

private theorem positive_initial_pderiv_of_zero_point_hs_persistence (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (1+t)))) (e : Fin (1+t))
    (hPersist : ∀ ℓ, hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal I univ e (fun _ => 0)) ℓ=hilbertSamuelValue I ℓ)
    (F : MvPowerSeries (Fin (1+t)) ℂ)
    (hF : F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (1+t)).toRingHom I)) :
    MvPowerSeries.pderiv ℂ e F∈
      actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (1+t)).toRingHom I) := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom (1+t)).toRingHom I
  let P := actualInitialVertexPolynomial K
  let r : Fin (1+t) ≃ Fin (1+t) := Equiv.swap 0 e
  let P' := fun a => MvPolynomial.rename r (P a)
  let J : Ideal (MvPowerSeries (Fin (1+t)) ℂ) := Ideal.span (range fun a => (P a : MvPowerSeries (Fin (1+t)) ℂ))
  let J' : Ideal (MvPowerSeries (Fin (1+t)) ℂ) := Ideal.span (range fun a => (P' a : MvPowerSeries (Fin (1+t)) ℂ))
  have hJ : actualHomogeneousInitialIdeal K=J := by
    rw [actualHomogeneousInitialIdeal_eq_initial_vertex_span]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext a
    exact (actualInitialVertexPolynomial_coe K a).symm
  have hline (p : ComplexModel (1+t)) (hp : p∈complexCoordinatePlane (1+t) 1) (ℓ : ℕ) :
      hilbertSamuelValue (polyTranslatedIdeal P' (fun i => p i)) ℓ=hilbertSamuelValue I ℓ := by
    have hq : (fun i => p (r i))=(fun i => p 0*(if i=e then 1 else 0)) := by
      funext i
      by_cases hi : i=e
      · subst i
        simp [r]
      · have hr0 : r i≠0 := by
          intro h
          have hre : r e=0 := by simp [r]
          exact hi (r.injective (h.trans hre.symm))
        have hv : 1≤(r i).val := by
          have hn : (r i).val≠0 := by intro he; exact hr0 (Fin.ext he)
          omega
        simp only [if_neg hi,mul_zero]
        exact hp (r i) hv
    have he := actualAmbientHS_eq_of_genuineAlgEquiv (permGerm r)
      (polyTranslatedIdeal P (fun i => p (r i))) ℓ
    rw [map_perm_polyTranslatedIdeal] at he
    rw [hq] at he
    exact he.trans (translated_cone_hs_eq_of_zero_point_persistence I e hPersist (p 0) ℓ)
  have hHS : ∀ p : ComplexModel (1+t), p∈complexCoordinatePlane (1+t) 1 → ∀ ℓ,
      hilbertSamuelValue (polyTranslatedIdeal P' (fun i => p i)) ℓ=
        hilbertSamuelValue (polyTranslatedIdeal P' 0) ℓ := by
    intro p hp ℓ
    have h0 := hline 0 (by intro i _; rfl) ℓ
    have hz : (fun i => (0 : ComplexModel (1+t)) i)=(0 : Fin (1+t) → ℂ) := by funext i; rfl
    rw [hz] at h0
    exact (hline p hp ℓ).trans h0.symm
  have hD : ∀ G∈J',MvPowerSeries.pderiv ℂ 0 G∈J' :=
    homogeneous_polynomial_span_pderiv_of_axis_hs P' (fun a => normalExponentDegree a.val)
      (fun a => (actualInitialVertexPolynomial_isHomogeneous K a).rename_isHomogeneous) hHS
  have hmap : Ideal.map (MvPowerSeries.renameEquiv ℂ r).toRingEquiv.toRingHom J=J' :=
    map_rename_polynomial_span r P
  have hgen (a : actualInitialVertices MonomialOrder.degLex K) :
      MvPowerSeries.pderiv ℂ e (P a : MvPowerSeries (Fin (1+t)) ℂ)∈J := by
    have ha : (P' a : MvPowerSeries (Fin (1+t)) ℂ)∈J' := Ideal.subset_span ⟨a,rfl⟩
    have hd := hD _ ha
    have he : MvPowerSeries.pderiv ℂ 0 (P' a : MvPowerSeries (Fin (1+t)) ℂ)=
        MvPowerSeries.rename r (MvPowerSeries.pderiv ℂ e (P a : MvPowerSeries (Fin (1+t)) ℂ)) := by
      rw [MvPowerSeries.pderiv_coe,MvPowerSeries.pderiv_coe,MvPowerSeries.rename_coe]
      have hh := MvPolynomial.pderiv_rename r.injective e (P a)
      have hre : r e=0 := by simp [r]
      rw [hre] at hh
      exact congrArg (fun Q : MvPolynomial (Fin (1+t)) ℂ => (Q : MvPowerSeries (Fin (1+t)) ℂ)) hh
    rw [he,←hmap] at hd
    exact (Ideal.apply_mem_of_equiv_iff (f := (MvPowerSeries.renameEquiv ℂ r).toRingEquiv)).mp hd
  rw [hJ] at hF ⊢
  induction hF using Submodule.span_induction with
  | mem G hG => obtain ⟨a,rfl⟩ := hG; exact hgen a
  | zero => rw [map_zero]; exact J.zero_mem
  | add G H _ _ hG hH => simpa only [map_add] using J.add_mem hG hH
  | smul A G hG ih =>
    change MvPowerSeries.pderiv ℂ e (A*G)∈J
    rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul]
    exact J.add_mem (J.mul_mem_left A ih) (J.mul_mem_right _ hG)

theorem initial_pderiv_of_zero_point_hs_persistence
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n)
    (hPersist : ∀ ℓ, hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal I univ e (fun _ => 0)) ℓ=hilbertSamuelValue I ℓ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) :
    MvPowerSeries.pderiv ℂ e F∈
      actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) := by
  obtain ⟨t,hn⟩ : ∃ t,n=1+t := ⟨n-1,by have he := e.isLt; omega⟩
  subst n
  exact positive_initial_pderiv_of_zero_point_hs_persistence t I e hPersist F hF

theorem coneSheaf_translated_origin (K : Ideal (MvPowerSeries (Fin n) ℂ)) (p : ComplexModel n) :
    HironakaRelativeNormalDeformationInitialRelations.originalCoherentOriginIdeal
      (HironakaRelativeNormalCoherentTranslatedJets.actualTranslatedOriginalSheaf (coneSheaf K) p)=
      actualUnshiftedTranslatedInitialIdeal K (fun i => p i) := by
  let v := (Fintype.equivFin (actualInitialVertices MonomialOrder.degLex K)).symm
  let H := fun i => coneFunctions K (v i)
  have hH : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (H i) univ := by
    intro i
    exact ((polyFunction_contDiff (actualInitialVertexPolynomial K (v i))).contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  have hrange : range H=range (coneFunctions K) := by
    ext f
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨v i,rfl⟩
    · rintro ⟨a,rfl⟩; obtain ⟨i,rfl⟩ := v.surjective a; exact ⟨i,rfl⟩
  have hgen : ∀ z∈(univ : Set (ComplexModel n)),∀ f,
      (coneSheaf K).mem z f ↔ IsInSpanAt (n := n) (· ∈ range H) z f := by
    intro z _ f
    rw [hrange]
    rfl
  let hhol := fun i => HironakaSmoothCentreCoherentDomain.translated_function_holAt
    isOpen_univ (hH i) (mem_univ p)
  have hI := HironakaSmoothCentreCoherentDomain.translated_origin_ideal_eq_span_of_real_generators
    (coneSheaf K) H isOpen_univ hH hgen (mem_univ p) hhol
  have hterm i : HolGerm.mk (H i ∘ HironakaRelativeNormalCoherentTranslatedJets.actualAffineTranslation n p) (hhol i)=
      actualUnshiftedTranslatedPolynomialEval n (fun j => p j) (actualInitialVertexPolynomial K (v i)) := by
    rw [translated_poly_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg (H i) (add_comm p z)
  rw [hI,actualUnshiftedTranslatedInitialIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change HolGerm.mk (H i ∘ HironakaRelativeNormalCoherentTranslatedJets.actualAffineTranslation n p) (hhol i)∈_
    rw [hterm]
    exact Ideal.subset_span ⟨v i,rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    obtain ⟨i,rfl⟩ := v.surjective a
    change actualUnshiftedTranslatedPolynomialEval n (fun j => p j) (actualInitialVertexPolynomial K (v i))∈_
    rw [←hterm i]
    exact Ideal.subset_span ⟨i,rfl⟩

end
end Hironaka.HironakaActualPersistentPointConeDerivatives
