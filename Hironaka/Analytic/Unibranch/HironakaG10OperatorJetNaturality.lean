import Hironaka.Analytic.Unibranch.HironakaG10BanachBilinearJetNaturality

/-! # Actual operator-composition and inverse identities after parameter jets -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality
open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteRank
  Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension
  Hironaka.Analytic.Unibranch.HironakaG10BanachBilinearJetNaturality

/-- Whole parameter jets only depend on the actual germ of the Banach family. -/
theorem banachJet_congr_eventually
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    {f g : ComplexModel d → E} (h : f =ᶠ[𝓝 (0 : ComplexModel d)] g) :
    banachJet d q φ f = banachJet d q φ g := by
  classical
  simp only [banachJet]
  apply Finset.sum_congr rfl
  intro k hk
  rw [(h.iteratedFDeriv ℂ k).self_of_nhds]

/-- A constant Banach family has the exact constant pure-tensor jet. -/
theorem banachJet_const
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (e : E) :
    banachJet d q φ (fun _ => e) = (1 : Γ) ⊗ₜ[ℂ] e := by
  have h := banachJet_smul_const d q φ hφ (fun _ => (1 : ℂ))
    (Eventually.of_forall fun _ => differentiableAt_const 1) e
  have h1 : HolGerm.mk (fun _ : ComplexModel d => (1 : ℂ))
      (Eventually.of_forall fun _ => differentiableAt_const 1) = 1 := by
    change HolGerm.mk (1 : ComplexModel d → ℂ) _ = 1
    exact HolGerm.mk_one
  simpa only [h1, map_one, one_smul] using h

/-- Parameter jets commute with composition of actual holomorphic families
of bounded operators. -/
theorem banachJet_operator_comp
    {Γ E F G : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (A : ComplexModel d → (F →L[ℂ] G)) (B : ComplexModel d → (E →L[ℂ] F))
    (hA : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ A z)
    (hB : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ B z) :
    banachJet d q φ (fun z => (A z).comp (B z)) =
      tensorBilinear (ContinuousLinearMap.compL ℂ E F G) (banachJet d q φ A)
        (banachJet d q φ B) := by
  exact banachJet_bilinear d q φ hφ (ContinuousLinearMap.compL ℂ E F G) A B hA hB

/-- If two actual holomorphic operator families are mutual inverses near the
origin, their parameter tensor jets are mutual inverses under the actual
extended composition operation. -/
theorem banachJet_operator_inverse
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (A B : ComplexModel d → (E →L[ℂ] E))
    (hA : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ A z)
    (hB : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ B z)
    (hAB : ∀ᶠ z in 𝓝 (0 : ComplexModel d), (A z).comp (B z) = ContinuousLinearMap.id ℂ E)
    (hBA : ∀ᶠ z in 𝓝 (0 : ComplexModel d), (B z).comp (A z) = ContinuousLinearMap.id ℂ E) :
    tensorBilinear (ContinuousLinearMap.compL ℂ E E E) (banachJet d q φ A) (banachJet d q φ B) =
        (1 : Γ) ⊗ₜ[ℂ] ContinuousLinearMap.id ℂ E ∧
    tensorBilinear (ContinuousLinearMap.compL ℂ E E E) (banachJet d q φ B) (banachJet d q φ A) =
        (1 : Γ) ⊗ₜ[ℂ] ContinuousLinearMap.id ℂ E := by
  constructor
  · rw [← banachJet_operator_comp d q φ hφ A B hA hB,
      banachJet_congr_eventually d q φ hAB, banachJet_const d q φ hφ]
  · rw [← banachJet_operator_comp d q φ hφ B A hB hA,
      banachJet_congr_eventually d q φ hBA, banachJet_const d q φ hφ]

end Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality
