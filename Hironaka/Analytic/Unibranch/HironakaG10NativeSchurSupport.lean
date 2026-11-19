import Hironaka.Analytic.Unibranch.HironakaG10NativeSourceSchurScalarSections
import Hironaka.Analytic.Unibranch.HironakaG10SchurSupportDirectExact
import Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10NativeSchurSupport
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
  Hironaka.Analytic.Unibranch.HironakaG10SchurSupportDirectExact
noncomputable section

theorem native_corrected_directExact_near_schur_support
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁₀ : K₁ ⊆ interior K₀)
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
    let Fm := fun s i j => restrictParam K₁ (hF i j) s
    let G := restrictMatrix K₁ hK₁₀ G₀ hG₀
    ∀ᶠ p in 𝓝 (0 : ComplexModel d),
      (opC ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
        (matrixOperator (Fm p))).IsInvertible →
      schurOp ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
        (matrixOperator (Fm p)) = 0 →
      DirectExact (kerFamily Fm G R₀ S₀ 0 p) (Fm p) := by
  let Fm := fun s i j => restrictParam K₁ (hF i j) s
  let G := restrictMatrix K₁ hK₁₀ G₀ hG₀
  have hK₁O : ∀ z ∈ K₁, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hK₁₀ hz))
  have hnear : ∀ᶠ s in 𝓝 (0 : ComplexModel d), ∀ z ∈ K₁, (s,z) ∈ O :=
    eventually_forall_mem_of_isOpen (isCompact_iff_compactSpace.mpr inferInstance) hO hK₁O
  have hFm : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ Fm s := by
    filter_upwards [hnear] with s hs
    exact differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      differentiableAt_restrictParam K₁ hO (hF i j) hs
  have hFm0 : Fm 0 = restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
      (zeroFibre_holomorphic d t hO hF hK₀) := by
    funext i j
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    rw [restrictParam_apply K₁ (hF i j) hK₁O z]
    rfl
  have hex' : DirectExact G (Fm 0) := by simpa only [G,hFm0] using hex
  have hS' : ∀ e, matrixOperator (Fm 0) (S₀ (matrixOperator (Fm 0) e)) = matrixOperator (Fm 0) e := by
    simpa only [hFm0] using hS
  exact kernel_family_directExact_on_nearby_schur_support Fm 0 G hFm hex' R₀ hR S₀ hS'
end
end Hironaka.Analytic.Unibranch.HironakaG10NativeSchurSupport
