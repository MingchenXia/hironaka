import Hironaka.Analytic.Unibranch.HironakaG10ActualInverseJetAtInvertible
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientOpCJet
import Hironaka.Resolution.HironakaG10LocFrischLocus

/-! # The actual Frisch Schur operator after finite parameter substitution -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJetAtInvertible
open Hironaka Hironaka
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension
  Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality
  Hironaka.Analytic.Unibranch.HironakaG10ActualInverseJetAtInvertible
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientOpCJet
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators

/-- The actual holomorphic Frisch Schur operator has the explicitly composed
whole parameter jet, using the actual nearby inverse family. -/
theorem banachJet_actual_schur_of_invertible
    {Γ E₁ E₀ : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : (opC P Q S₀ (f 0)).IsInvertible) :
    banachJet d q φ (fun z => schurOp P Q S₀ (f z)) =
      tensorBilinear (ContinuousLinearMap.compL ℂ E₁ E₀ E₀)
        ((1 : Γ) ⊗ₜ[ℂ] (ContinuousLinearMap.id ℂ E₀ - Q))
        (tensorBilinear (ContinuousLinearMap.compL ℂ E₁ E₀ E₀)
          (banachJet d q φ (fun z => (opC P Q S₀ (f z)).inverse))
          (banachJet d q φ f)) := by
  let C := fun z => opC P Q S₀ (f z)
  have hC : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ C z := by
    filter_upwards [hf] with z hz
    exact (hz.clm_comp (differentiableAt_const _)).add (differentiableAt_const _)
  have hCi : ∀ᶠ z in 𝓝 (0 : ComplexModel d), (C z).IsInvertible :=
    hC.self_of_nhds.continuousAt (show {T : E₀ →L[ℂ] E₀ | T.IsInvertible} ∈ 𝓝 (C 0) by
      obtain ⟨e, he⟩ := hC0
      have hn : Set.range ((↑) : (E₀ ≃L[ℂ] E₀) → E₀ →L[ℂ] E₀) ∈ 𝓝 (C 0) := by
        change Set.range ((↑) : (E₀ ≃L[ℂ] E₀) → E₀ →L[ℂ] E₀) ∈ 𝓝 (opC P Q S₀ (f 0))
        rw [← he]
        exact ContinuousLinearEquiv.nhds e
      filter_upwards [hn] with T ⟨e', he'⟩
      exact ⟨e', he'⟩)
  have hI : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun z => (C z).inverse) z := by
    filter_upwards [hC,hCi] with z hz hzi
    exact ((hzi.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp z hz
  have hinner : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun z => (C z).inverse.comp (f z)) z := by
    filter_upwards [hI,hf] with z hz hfz
    exact hz.clm_comp hfz
  have hc : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun _ => ContinuousLinearMap.id ℂ E₀ - Q) z :=
    Eventually.of_forall fun _ => differentiableAt_const _
  change banachJet d q φ (fun z => (ContinuousLinearMap.id ℂ E₀ - Q).comp
      ((C z).inverse.comp (f z))) = _
  rw [banachJet_operator_comp d q φ hφ _ _ hc hinner,
    banachJet_const d q φ hφ,
    banachJet_operator_comp d q φ hφ _ _ hI hf]

/-- The original Schur family acts on every coefficient vector as the
composition of its three original, scalar-extended operator jets. -/
theorem coefficientTensorOperator_actual_schur_of_invertible
    {Γ E₁ E₀ ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : (opC P Q S₀ (f 0)).IsInvertible) :
    coefficientTensorOperator (E := E₁) (F := E₀) b
      (banachJet (E := E₁ →L[ℂ] E₀) d q φ (fun z => schurOp P Q S₀ (f z))) =
      (coefficientCLM (ContinuousLinearMap.id ℂ E₀ - Q)).toLinearMap.comp
        ((coefficientTensorOperator (E := E₀) (F := E₀) b
          (banachJet (E := E₀ →L[ℂ] E₀) d q φ (fun z => (opC P Q S₀ (f z)).inverse))).comp
          (coefficientTensorOperator (E := E₁) (F := E₀) b (banachJet (E := E₁ →L[ℂ] E₀) d q φ f))) := by
  rw [banachJet_actual_schur_of_invertible d q φ hφ P Q S₀ f hf hC0,
    coefficientTensorOperator_comp, coefficientTensorOperator_comp,
    coefficientTensorOperator_one]

/-- The finite coefficient comparison operator is invertible and its
inverse is the coefficient action of the actual holomorphic inverse jet. -/
theorem coefficient_actual_inverse_jet_of_invertible
    {Γ E₁ E₀ ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤ RingHom.ker φ.toRingHom)
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : (opC P Q S₀ (f 0)).IsInvertible)
    (F : (ι → E₁) →L[ℂ] (ι → E₀))
    (hF : coefficientTensorOperator b (banachJet d q φ f) = F.toLinearMap) :
    let C := opC (coefficientCLM P) (coefficientCLM Q) (coefficientCLM S₀) F
    C.IsInvertible ∧
      coefficientTensorOperator b (banachJet d q φ (fun z => (opC P Q S₀ (f z)).inverse)) =
        C.inverse.toLinearMap := by
  let A := (ContinuousLinearMap.id ℂ E₁ - P).comp S₀
  let B := ContinuousLinearMap.id ℂ E₀ - Q
  have hC : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun z => opC P Q S₀ (f z)) z := by
    filter_upwards [hf] with z hz
    have hcomp := ((ContinuousLinearMap.compL ℂ E₀ E₁ E₀).flip A).differentiableAt.comp z hz
    change DifferentiableAt ℂ (fun z => (f z).comp A + B) z
    exact hcomp.add (differentiableAt_const B)
  let C := opC (coefficientCLM P) (coefficientCLM Q) (coefficientCLM S₀) F
  let U := coefficientTensorOperator b (banachJet d q φ (fun z => opC P Q S₀ (f z)))
  let V := coefficientTensorOperator b (banachJet d q φ (fun z => (opC P Q S₀ (f z)).inverse))
  have hU : U = C.toLinearMap := coefficient_opC_jet b d q φ hφ P Q S₀ f hf F hF
  obtain ⟨hUV,hVU⟩ := banachJet_actual_inverse_of_invertible d q φ hφ (fun z => opC P Q S₀ (f z)) hC hC0
  have hUV' : U.comp V = LinearMap.id := by
    have h := congrArg (coefficientTensorOperator (E := E₀) (F := E₀) b) hUV
    rw [coefficientTensorOperator_comp,coefficientTensorOperator_one] at h
    simpa [U,V,coefficientCLM] using h
  have hVU' : V.comp U = LinearMap.id := by
    have h := congrArg (coefficientTensorOperator (E := E₀) (F := E₀) b) hVU
    rw [coefficientTensorOperator_comp,coefficientTensorOperator_one] at h
    simpa [U,V,coefficientCLM] using h
  rw [hU] at hUV' hVU'
  have hleft : Function.LeftInverse V C := fun v => by
    have h := LinearMap.congr_fun hVU' v
    simpa using h
  have hright : Function.RightInverse V C := fun v => by
    have h := LinearMap.congr_fun hUV' v
    simpa using h
  have hbij : Function.Bijective C := ⟨hleft.injective,hright.surjective⟩
  have hCinvertible : C.IsInvertible := ⟨ContinuousLinearEquiv.ofBijective C (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2),rfl⟩
  refine ⟨hCinvertible,?_⟩
  apply LinearMap.ext
  intro x
  change V x = C.inverse x
  have h := hleft (C.inverse x)
  simpa only [hCinvertible.self_apply_inverse] using h

/-- The coefficient action of the actual holomorphic Schur jet is the
Schur operator of the original finite coefficient action. -/
theorem coefficient_actual_schur_jet_of_invertible
    {Γ E₁ E₀ ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤ RingHom.ker φ.toRingHom)
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : (opC P Q S₀ (f 0)).IsInvertible)
    (F : (ι → E₁) →L[ℂ] (ι → E₀))
    (hF : coefficientTensorOperator b (banachJet d q φ f) = F.toLinearMap) :
    coefficientTensorOperator b (banachJet d q φ (fun z => schurOp P Q S₀ (f z))) =
      (schurOp (coefficientCLM P) (coefficientCLM Q) (coefficientCLM S₀) F).toLinearMap := by
  obtain ⟨_hC,hInv⟩ := coefficient_actual_inverse_jet_of_invertible b d q φ hφ P Q S₀ f hf hC0 F hF
  rw [coefficientTensorOperator_actual_schur_of_invertible b d q φ hφ P Q S₀ f hf hC0, hInv, hF]
  ext v i
  simp [schurOp, coefficientCLM_apply]
end Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJetAtInvertible
