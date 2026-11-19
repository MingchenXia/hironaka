import Hironaka.Analytic.Unibranch.HironakaG10RadialNativeJet
import Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation
import Hironaka.Analytic.Unibranch.HironakaG10NativeFibreRestriction
import Hironaka.Analytic.Unibranch.HironakaG10TranslatedNativeGerm
import Hironaka.Analytic.Unibranch.HironakaG10TranslatedScalarIdeal

/-! Whole scalar-ideal necessity for the original family at an arbitrary parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TranslatedRadialNative
open Hironaka Hironaka
  HolGerm OkaRelationSheaf HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianBaseChange HironakaG10ArtinianFlatQuotient
  HironakaG10FlatPrivilegedEuclidean HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator Hironaka.Analytic.Unibranch.HironakaG10SourceCoefficientOperator
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJetAtInvertible Hironaka.Analytic.Unibranch.HironakaG10NativeSourceQuotientFlat
  Hironaka.Analytic.Unibranch.HironakaG10RadialNativeJet Hironaka.Analytic.Unibranch.HironakaG10CompactWindowRestriction
  Hironaka.Analytic.Unibranch.HironakaG10ScalarIdealJet
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation Hironaka.Analytic.Unibranch.HironakaG10NativeFibreRestriction
  Hironaka.Analytic.Unibranch.HironakaG10TranslatedNativeGerm Hironaka.Analytic.Unibranch.HironakaG10TranslatedScalarIdeal
  HironakaG10FlatPolydiscParametric OkaGermBridge
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

/-- The same nested-window necessity at an arbitrary parameter p, using the
original product stalk and the actual scalar-germ ideal at p. -/
theorem native_quotient_flat_forces_radial_scalar_ideal_at_parameter
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₂ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₂]
    (hK₂ : K₂ ∈ closedPolydiscs t) (hK₂₀ : K₂ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (p : ComplexModel d) (hp : ∀ z ∈ K₀, (p,z) ∈ O)
    (F₀ : Fin a → Fin b → holSubalgebra K₂) (G₀ : Fin b → Fin c → holSubalgebra K₂)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin b → holSubalgebra K₂) →L[ℂ] (Fin c → holSubalgebra K₂))
    (S₀ : (Fin a → holSubalgebra K₂) →L[ℂ] (Fin b → holSubalgebra K₂))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (Gr : Fin b → Fin c → holSubalgebra K₂)
    (hrel : ∀ z ∈ K₂, ∀ i l, ∑ j, F i j (p,z) * extendZero K₂ (Gr j l) z = 0)
    (hRef : (opA ((matrixOperator G₀).comp R₀) R₀ (matrixOperator Gr)).IsInvertible)
    (hC : (opC ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
      (sourceOperator d t (K₁ := K₂) hF p)).IsInvertible)
    (hSchurHol : ∀ᶠ s in 𝓝 p, DifferentiableAt ℂ
      (fun s => schurOp ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (sourceOperator d t (K₁ := K₂) hF s)) s)
    (I : Ideal (HolGerm (ComplexModel d)))
    (hflat : ∀ z ∈ K₂, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt (p,z) (F i j)))))) :
    Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₂) ×
        ((Fin a → holSubalgebra K₂) →L[ℂ] ℂ) =>
      let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₂) q.1)
      germAt p (L ∘ (fun s => schurOp ((matrixOperator G₀).comp R₀)
        ((matrixOperator F₀).comp S₀) S₀ (sourceOperator d t (K₁ := K₂) hF s)))) ≤ I := by
  let O' := (shiftJoint d t p) ⁻¹' O
  let F' := fun i j x => F i j (shiftJoint d t p x)
  have hO' : IsOpen O' := hO.preimage (continuous_shiftJoint d t p)
  let hF' : ∀ i j, DifferentiableOn ℂ (F' i j) O' := fun i j =>
    (hF i j).comp (differentiable_shiftJoint d t p).differentiableOn (fun _ h => h)
  have hp' : ∀ z ∈ K₀, (0,z) ∈ O' := by simpa [O',shiftJoint] using hp
  have hp₂ : ∀ z ∈ K₂, (p,z) ∈ O := fun z hz => hp z (interior_subset (hK₂₀ hz))
  let f := sourceOperator d t (K₁ := K₂) hF
  let f' := sourceOperator d t (K₁ := K₂) hF'
  let P := (matrixOperator G₀).comp R₀
  let Q := (matrixOperator F₀).comp S₀
  let S := fun s => schurOp P Q S₀ (f s)
  let T := fun s => schurOp P Q S₀ (f' s)
  have hshift : f' =ᶠ[𝓝 (0 : ComplexModel d)] fun s => f (p+s) :=
    sourceOperator_shift_eventually d t hO hF p hp₂
  have hST : T =ᶠ[𝓝 (0 : ComplexModel d)] fun s => S (p+s) :=
    hshift.mono fun s hs => congrArg (schurOp P Q S₀) hs
  have hcont : ContinuousAt (fun s : ComplexModel d => p+s) (0 : ComplexModel d) :=
    (show Continuous (fun s : ComplexModel d => p+s) from continuous_const.add continuous_id).continuousAt
  have htend : Tendsto (fun s : ComplexModel d => p+s) (𝓝 (0 : ComplexModel d)) (𝓝 p) := by
    simpa only [add_zero] using hcont.tendsto
  have hSh : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun s => S (p+s)) s := by
    filter_upwards [htend.eventually hSchurHol] with s hs
    exact hs.comp s ((differentiableAt_const p).add differentiableAt_id)
  have hTh : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ T s := by
    filter_upwards [hSh,hST.eventually_nhds] with s hs heq
    exact hs.congr_of_eventuallyEq heq
  have hC' : (opC P Q S₀ (f' 0)).IsInvertible := by
    have h0 := hshift.self_of_nhds
    simpa only [add_zero,h0] using hC
  have hrel' : ∀ z ∈ K₂, ∀ i l, ∑ j, F' i j (0,z) * extendZero K₂ (Gr j l) z = 0 := by
    simpa only [F',shiftJoint,add_zero] using hrel
  have hflat' : ∀ z ∈ K₂, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt (0,z) (F' i j))))) := by
    intro z hz
    have hentry : (fun i j => germAt (0,z) (F' i j)) = (fun i j => germAt (p,z) (F i j)) := by
      funext i j
      have hpz : (p,z) ∈ O := hp z (interior_subset (hK₂₀ hz))
      have hh : HolAt (F i j) (p,z) := by
        filter_upwards [hO.mem_nhds hpz] with x hx
        exact (hF i j x hx).differentiableAt (hO.mem_nhds hx)
      exact germAt_shiftJoint d t p z (F i j) hh
    rw [hentry]
    exact hflat z hz
  have hI' := native_quotient_flat_forces_radial_scalar_ideal d t hK₂ hK₂₀
    hO' hF' hp' F₀ G₀ hex R₀ S₀ hR hS Gr hrel' hRef hC' hTh I hflat'
  rw [translated_scalar_germ_ideal_eq d p S T hSchurHol hTh hST] at hI'
  exact hI'

end
end Hironaka.Analytic.Unibranch.HironakaG10TranslatedRadialNative
