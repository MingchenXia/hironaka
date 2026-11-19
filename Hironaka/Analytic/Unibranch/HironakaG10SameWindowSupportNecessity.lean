import Hironaka.Analytic.Unibranch.HironakaG10SameWindowSupportRelation
import Hironaka.Analytic.Unibranch.HironakaG10TranslatedRadialNative
import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SameWindowSupportNecessity
open Hironaka Hironaka
  HolGerm OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  HironakaG10FlatPrivilegedEuclidean HironakaG10FlatResolutionStart
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
  Hironaka.Analytic.Unibranch.HironakaG10SameWindowSupportRelation Hironaka.Analytic.Unibranch.HironakaG10TranslatedRadialNative
  OkaGermBridge
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen.basePullback d t).toAlgebra
theorem native_scalar_ideal_necessary_near_same_support
    (d t : ℕ) {a b c : ℕ} {K₀ K : Set (ComplexModel t)}
    [CompactSpace K₀] [CompactSpace K] (hK : K ∈ closedPolydiscs t) (hKK₀ : K ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (G₀ : Fin b → Fin c → ComplexModel t → ℂ)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀))
    (hex : DirectExact (restrictMatrix K hKK₀ G₀ hG₀)
      (restrictMatrix K hKK₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀)))
    (R₀ : (Fin b → holSubalgebra K) →L[ℂ] (Fin c → holSubalgebra K))
    (hR : ∀ e, matrixOperator (restrictMatrix K hKK₀ G₀ hG₀)
      (R₀ (matrixOperator (restrictMatrix K hKK₀ G₀ hG₀) e)) =
      matrixOperator (restrictMatrix K hKK₀ G₀ hG₀) e)
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin b → holSubalgebra K))
    (hS : ∀ e, matrixOperator (restrictMatrix K hKK₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀))
      (S₀ (matrixOperator (restrictMatrix K hKK₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀)) e)) =
      matrixOperator (restrictMatrix K hKK₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀)) e) :
    let F₀ := restrictMatrix K hKK₀ (fun i j x => F i j (0,x))
      (zeroFibre_holomorphic d t hO hF hK₀)
    let G := restrictMatrix K hKK₀ G₀ hG₀
    let f := sourceOperator d t (K₁ := K) hF
    let S := fun p => schurOp ((matrixOperator G).comp R₀) ((matrixOperator F₀).comp S₀) S₀ (f p)
    ∀ᶠ p in 𝓝 (0 : ComplexModel d), S p = 0 →
      ∀ I : Ideal (HolGerm (ComplexModel d)),
      (∀ z ∈ K, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
        ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
          ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
            (Matrix.mulVecLin (fun i j => germAt (p,z) (F i j)))))) →
      Ideal.span (Set.range fun q : (Fin b → holSubalgebra K) ×
          ((Fin a → holSubalgebra K) →L[ℂ] ℂ) =>
        let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K) q.1)
        germAt p (L ∘ S)) ≤ I := by
  let F₀ := restrictMatrix K hKK₀ (fun i j x => F i j (0,x))
      (zeroFibre_holomorphic d t hO hF hK₀)
  let G := restrictMatrix K hKK₀ G₀ hG₀
  let f := sourceOperator d t (K₁ := K) hF
  let Fm := fun s i j => restrictParam K (hF i j) s
  let S := fun p => schurOp ((matrixOperator G).comp R₀) ((matrixOperator F₀).comp S₀) S₀ (f p)
  have hKO : ∀ z ∈ K, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hKK₀ hz))
  have hf := sourceOperator_holomorphic d t hO hF hKO
  have hf0 : f 0 = matrixOperator F₀ := sourceOperator_zero d t hKK₀ hO hF hK₀
  have hcomp : ∀ e, matrixOperator F₀ (matrixOperator G e) = 0 :=
    matrixOperator_comp_apply _ _ hex.comp
  have hC0 : opC ((matrixOperator G).comp R₀) ((matrixOperator F₀).comp S₀) S₀ (f 0) =
      ContinuousLinearMap.id ℂ _ := by rw [hf0]; exact opC_self hcomp
  have hSnear : ∀ᶠ p in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ S p :=
    actual_schur_holomorphic d ((matrixOperator G).comp R₀) ((matrixOperator F₀).comp S₀) S₀ f hf hC0
  have htube : ∀ᶠ p in 𝓝 (0 : ComplexModel d), ∀ z ∈ K₀, (p,z) ∈ O :=
    eventually_forall_mem_of_isOpen (isCompact_iff_compactSpace.mpr inferInstance) hO hK₀
  have hFm0 : Fm 0 = F₀ := by
    funext i j
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    rw [restrictParam_apply K (hF i j) hKO z]
    rfl
  have hproducer := same_window_corrected_relation_near_support d t hKK₀ hO hF hK₀ G₀ hG₀ hex R₀ hR S₀ hS
  filter_upwards [hproducer,htube,hSnear.eventually_nhds] with p hp hpTube hpHol
  intro hpS I hpflat
  have hpS' : schurOp ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
      (matrixOperator (Fm p)) = 0 := by
    rw [hFm0]
    exact hpS
  obtain ⟨Gr,_,hRef,hrel⟩ := hp.2 hpS'
  have hC : (opC ((matrixOperator G).comp R₀) ((matrixOperator F₀).comp S₀) S₀ (f p)).IsInvertible := by
    have hpC := hp.1
    change (opC ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
      (matrixOperator (Fm p))).IsInvertible at hpC
    rw [hFm0] at hpC
    exact hpC
  exact native_quotient_flat_forces_radial_scalar_ideal_at_parameter d t hK hKK₀ hO hF p hpTube
    F₀ G hex R₀ S₀ hR hS Gr hrel hRef hC hpHol I hpflat

end
end Hironaka.Analytic.Unibranch.HironakaG10SameWindowSupportNecessity
