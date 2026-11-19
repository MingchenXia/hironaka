import Hironaka.Analytic.Unibranch.HironakaG10TranslatedFixedSchurNativeFlat
import Hironaka.Analytic.Unibranch.HironakaG10NativeSchurSupport
import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic
import Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10NativeFixedSchurNearbySufficiency
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaRelativeNormalIdeal
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric HironakaG10FlatPrivilegedEuclidean
  HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
  Hironaka.Analytic.Unibranch.HironakaG10NativeSchurSupport Hironaka.Analytic.Unibranch.HironakaG10TranslatedFixedSchurNativeFlat
noncomputable section
local instance (d : ℕ) : Algebra ℂ (HolGerm (ComplexModel d)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel d)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

theorem original_fixed_schur_ideal_suffices_near_support
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁ : K₁ ∈ closedPolydiscs t) (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (G₀ : Fin b → Fin c → ComplexModel t → ℂ)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀))
    (hex : DirectExact (restrictMatrix K₁ hK₁₀ G₀ hG₀)
      (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x)) (zeroFibre_holomorphic d t hO hF hK₀)))
    (R₀ : (Fin b → holSubalgebra K₁) →L[ℂ] (Fin c → holSubalgebra K₁))
    (hR : ∀ e, matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀)
      (R₀ (matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀) e)) =
      matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀) e)
    (S₀ : (Fin a → holSubalgebra K₁) →L[ℂ] (Fin b → holSubalgebra K₁))
    (hS : ∀ e, matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
      (zeroFibre_holomorphic d t hO hF hK₀))
      (S₀ (matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀)) e)) =
      matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀)) e) :
    let f₀ := matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
      (zeroFibre_holomorphic d t hO hF hK₀))
    let g₀ := matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀)
    let f := sourceOperator d t (K₁ := K₁) hF
    let S := fun p => schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ (f p)
    ∀ᶠ p in 𝓝 (0 : ComplexModel d), ∀ I : Ideal (HolGerm (ComplexModel d)),
      S p = 0 →
      Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
          ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
        let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
        germAt p (L ∘ S)) ≤ I →
      ∀ z ∈ interior K₁, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
        ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
          ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
            (Matrix.mulVecLin (fun i j => germAt (p,z) (F i j))))) := by
  let Fm := fun s i j => restrictParam K₁ (hF i j) s
  let G := restrictMatrix K₁ hK₁₀ G₀ hG₀
  let F₀ := restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
    (zeroFibre_holomorphic d t hO hF hK₀)
  let f₀ := matrixOperator F₀
  let g₀ := matrixOperator G
  let f := sourceOperator d t (K₁ := K₁) hF
  let S := fun p => schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ (f p)
  have hK₁O : ∀ z ∈ K₁, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hK₁₀ hz))
  have hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f s :=
    sourceOperator_holomorphic d t hO hF hK₁O
  have hf0 : f 0 = f₀ := sourceOperator_zero d t hK₁₀ hO hF hK₀
  have hcomp : ∀ e, f₀ (g₀ e) = 0 := matrixOperator_comp_apply _ _ hex.comp
  have hC0 : opC (g₀.comp R₀) (f₀.comp S₀) S₀ (f 0) = ContinuousLinearMap.id ℂ _ := by
    rw [hf0]
    exact opC_self hcomp
  have hTnear : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ S s :=
    actual_schur_holomorphic d (g₀.comp R₀) (f₀.comp S₀) S₀ f hf hC0
  have hCcont : ContinuousAt (fun s => opC (g₀.comp R₀) (f₀.comp S₀) S₀ (f s)) 0 :=
    ((hf.self_of_nhds.continuousAt.clm_comp continuousAt_const).add continuousAt_const)
  have hCnear : ∀ᶠ p in 𝓝 (0 : ComplexModel d),
      (opC (g₀.comp R₀) (f₀.comp S₀) S₀ (f p)).IsInvertible :=
    hCcont (show {T : (Fin a → holSubalgebra K₁) →L[ℂ] (Fin a → holSubalgebra K₁) | T.IsInvertible} ∈
      𝓝 (opC (g₀.comp R₀) (f₀.comp S₀) S₀ (f 0)) by rw [hC0]; exact isInvertible_mem_nhds_id)
  have hTube : ∀ᶠ p in 𝓝 (0 : ComplexModel d), ∀ z ∈ K₀, (p,z) ∈ O :=
    eventually_forall_mem_of_isOpen (isCompact_iff_compactSpace.mpr inferInstance) hO hK₀
  have hSupp := native_corrected_directExact_near_schur_support d t hK₁₀ hO hF hK₀ G₀ hG₀ hex R₀ hR S₀ hS
  have hFm0 : Fm 0 = F₀ := by
    funext i j
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    rw [restrictParam_apply K₁ (hF i j) hK₁O z]
    rfl
  filter_upwards [hCnear,hTube,hTnear.eventually_nhds,hSupp] with p hpC hpO hpHol hpSupp
  intro I hpS hpI
  have hfEq (s : ComplexModel d) : f s = matrixOperator (Fm s) := rfl
  have hf0Eq : f₀ = matrixOperator F₀ := rfl
  have hpC' : (opC (g₀.comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
      (matrixOperator (Fm p))).IsInvertible := by
    rw [hFm0, ← hf0Eq, ← hfEq p]
    exact hpC
  have hpS' : schurOp (g₀.comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
      (matrixOperator (Fm p)) = 0 := by
    rw [hFm0, ← hf0Eq, ← hfEq p]
    exact hpS
  have hDs := hpSupp hpC' hpS'
  have hD : DirectExact
      (fun j l => kerSec (g₀.comp R₀) (f₀.comp S₀) S₀ (f p) (fun j' => G j' l) j)
      (fun i j => restrictParam K₁ (hF i j) p) := by
    change DirectExact (fun j l => kerSec ((matrixOperator G).comp R₀)
      ((matrixOperator (Fm 0)).comp S₀) S₀ (matrixOperator (Fm p)) (fun j' => G j' l) j) (Fm p) at hDs
    rw [hFm0, ← hf0Eq, ← hfEq p] at hDs
    exact hDs
  exact fixed_schur_ideal_forces_native_flat_at_parameter d t hK₁ hK₁₀ hO hF p hpO
    F₀ G hex R₀ S₀ hR hS I hpC hpHol hpI hD
end
end Hironaka.Analytic.Unibranch.HironakaG10NativeFixedSchurNearbySufficiency
