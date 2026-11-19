import Hironaka.Analytic.Unibranch.HironakaG10VaryingSourceWholeFlat
import Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation
import Hironaka.Analytic.Unibranch.HironakaG10NativeFibreRestriction
import Hironaka.Analytic.Unibranch.HironakaG10TranslatedNativeGerm
import Hironaka.Analytic.Unibranch.HironakaG10TranslatedScalarIdeal
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TranslatedFixedSchurNativeFlat
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaRelativeNormalIdeal
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  HironakaG10FlatPrivilegedEuclidean HironakaG10FlatResolutionStart
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation
  Hironaka.Analytic.Unibranch.HironakaG10NativeFibreRestriction
  Hironaka.Analytic.Unibranch.HironakaG10TranslatedNativeGerm
  Hironaka.Analytic.Unibranch.HironakaG10TranslatedScalarIdeal
  Hironaka.Analytic.Unibranch.HironakaG10VaryingSourceWholeFlat
noncomputable section
local instance (d : ℕ) : Algebra ℂ (HolGerm (ComplexModel d)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel d)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

theorem fixed_schur_ideal_forces_native_flat_at_parameter
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁ : K₁ ∈ closedPolydiscs t) (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (p : ComplexModel d) (hp : ∀ z ∈ K₀, (p,z) ∈ O)
    (F₀ : Fin a → Fin b → holSubalgebra K₁) (G₀ : Fin b → Fin c → holSubalgebra K₁)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin b → holSubalgebra K₁) →L[ℂ] (Fin c → holSubalgebra K₁))
    (S₀ : (Fin a → holSubalgebra K₁) →L[ℂ] (Fin b → holSubalgebra K₁))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (I : Ideal (HolGerm (ComplexModel d)))
    (hC : (opC ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
      (sourceOperator d t (K₁ := K₁) hF p)).IsInvertible)
    (hSchurHol : ∀ᶠ s in 𝓝 p, DifferentiableAt ℂ
      (fun s => schurOp ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (sourceOperator d t (K₁ := K₁) hF s)) s)
    (hI : Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
      let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
      germAt p (L ∘ (fun s => schurOp ((matrixOperator G₀).comp R₀)
        ((matrixOperator F₀).comp S₀) S₀ (sourceOperator d t (K₁ := K₁) hF s)))) ≤ I)
    (hDirect : DirectExact
      (fun j l => kerSec ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (sourceOperator d t (K₁ := K₁) hF p) (fun j' => G₀ j' l) j)
      (fun i j => restrictParam K₁ (hF i j) p)) :
    ∀ z ∈ interior K₁, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt (p,z) (F i j))))) := by
  let O' := (shiftJoint d t p) ⁻¹' O
  let F' := fun i j x => F i j (shiftJoint d t p x)
  have hO' : IsOpen O' := hO.preimage (continuous_shiftJoint d t p)
  let hF' : ∀ i j, DifferentiableOn ℂ (F' i j) O' := fun i j =>
    (hF i j).comp (differentiable_shiftJoint d t p).differentiableOn (fun _ h => h)
  have hp' : ∀ z ∈ K₀, (0,z) ∈ O' := by simpa [O',shiftJoint] using hp
  have hp₁ : ∀ z ∈ K₁, (p,z) ∈ O := fun z hz => hp z (interior_subset (hK₁₀ hz))
  let f := sourceOperator d t (K₁ := K₁) hF
  let f' := sourceOperator d t (K₁ := K₁) hF'
  let P := (matrixOperator G₀).comp R₀
  let Q := (matrixOperator F₀).comp S₀
  let S := fun s => schurOp P Q S₀ (f s)
  let T := fun s => schurOp P Q S₀ (f' s)
  have hshift : f' =ᶠ[𝓝 (0 : ComplexModel d)] fun s => f (p+s) :=
    sourceOperator_shift_eventually d t hO hF p hp₁
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
  have hI' : Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
      let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
      HolGerm.mk (L ∘ T) (hTh.mono fun _ h => L.differentiableAt.comp _ h)) ≤ I := by
    rw [translated_scalar_germ_ideal_eq d p S T hSchurHol hTh hST]
    exact hI
  have hC' : (opC P Q S₀ (f' 0)).IsInvertible := by
    have h0 := hshift.self_of_nhds
    simpa only [add_zero,h0] using hC
  have hFm : (fun i j => restrictParam K₁ (hF i j) p) =
      restrictMatrix K₁ hK₁₀ (fun i j z => F' i j (0,z))
        (Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur.zeroFibre_holomorphic d t hO' hF' hp') := by
    rw [restrictParam_eq_fibreRestriction d t hK₁₀ hO hF p hp]
    funext i j
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    simp [restrictMatrix, F', shiftJoint]
  have hDirect' : DirectExact
      (fun j l => kerSec P Q S₀
        (matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j z => F' i j (0,z))
          (Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur.zeroFibre_holomorphic d t hO' hF' hp')))
        (fun j' => G₀ j' l) j)
      (restrictMatrix K₁ hK₁₀ (fun i j z => F' i j (0,z))
        (Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur.zeroFibre_holomorphic d t hO' hF' hp')) := by
    rw [← hFm]
    exact hDirect
  intro z hz
  have hflat := varying_scalar_ideal_forces_native_quotient_flat d t hK₁ hK₁₀ hO' hF' hp'
    F₀ G₀ hex R₀ S₀ hR hS I hC' hTh hI' hDirect' z hz
  have hentry : (fun i j => germAt (0,z) (F' i j)) = (fun i j => germAt (p,z) (F i j)) := by
    funext i j
    have hpz : (p,z) ∈ O := hp z (interior_subset (hK₁₀ (interior_subset hz)))
    have hh : HolAt (F i j) (p,z) := by
      filter_upwards [hO.mem_nhds hpz] with x hx
      exact (hF i j x hx).differentiableAt (hO.mem_nhds hx)
    exact germAt_shiftJoint d t p z (F i j) hh
  rw [hentry] at hflat
  exact hflat
end
end Hironaka.Analytic.Unibranch.HironakaG10TranslatedFixedSchurNativeFlat
