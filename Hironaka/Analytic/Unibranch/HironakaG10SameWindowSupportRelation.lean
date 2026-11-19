import Hironaka.Analytic.Unibranch.HironakaG10NativeSchurSupport
import Hironaka.Analytic.Unibranch.HironakaG10NearbyCorrectedComparison
import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJetAtInvertible
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10SameWindowSupportRelation
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10NativeSchurSupport
  Hironaka.Analytic.Unibranch.HironakaG10NearbyCorrectedComparison
  Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
noncomputable section

/-- On the same old Schur support, construct the corrected relation and its
old-reference invertibility; no independent relation or comparison is assumed. -/
theorem same_window_corrected_relation_near_support
    (d t : ℕ) {a b c : ℕ} {K₀ K : Set (ComplexModel t)}
    [CompactSpace K₀] [CompactSpace K] (hKK₀ : K ⊆ interior K₀)
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
    let Fm := fun s i j => restrictParam K (hF i j) s
    let G := restrictMatrix K hKK₀ G₀ hG₀
    ∀ᶠ p in 𝓝 (0 : ComplexModel d),
      (opC ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
        (matrixOperator (Fm p))).IsInvertible ∧
      (schurOp ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
        (matrixOperator (Fm p)) = 0 →
        ∃ Gr : Fin b → Fin c → holSubalgebra K,
          DirectExact Gr (Fm p) ∧
          (opA ((matrixOperator G).comp R₀) R₀ (matrixOperator Gr)).IsInvertible ∧
          ∀ z ∈ K, ∀ i l, ∑ j, F i j (p,z) * extendZero K (Gr j l) z = 0) := by
  let Fm := fun s i j => restrictParam K (hF i j) s
  let G := restrictMatrix K hKK₀ G₀ hG₀
  have hKO : ∀ z ∈ K, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hKK₀ hz))
  have hnear : ∀ᶠ p in 𝓝 (0 : ComplexModel d), ∀ z ∈ K, (p,z) ∈ O :=
    eventually_forall_mem_of_isOpen (isCompact_iff_compactSpace.mpr inferInstance) hO hKO
  have hFm : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ Fm s := by
    filter_upwards [hnear] with s hs
    exact differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      differentiableAt_restrictParam K hO (hF i j) hs
  have hFm0 : Fm 0 = restrictMatrix K hKK₀ (fun i j x => F i j (0,x))
      (zeroFibre_holomorphic d t hO hF hK₀) := by
    funext i j
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    rw [restrictParam_apply K (hF i j) hKO z]
    rfl
  have hex' : DirectExact G (Fm 0) := by simpa only [G,hFm0] using hex
  have hS' : ∀ e, matrixOperator (Fm 0) (S₀ (matrixOperator (Fm 0) e)) = matrixOperator (Fm 0) e := by
    simpa only [hFm0] using hS
  have hcomp : ∀ e, matrixOperator (Fm 0) (matrixOperator G e) = 0 :=
    matrixOperator_comp_apply _ _ hex'.comp
  have hC0 : opC ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
      (matrixOperator (Fm 0)) = ContinuousLinearMap.id ℂ _ := opC_self hcomp
  have hFcont : ContinuousAt (fun p => matrixOperator (Fm p)) 0 :=
    (matrixOperatorCLM (R := holSubalgebra K) (p := Fin b) (q := Fin a)).continuous.continuousAt.comp
      hFm.self_of_nhds.continuousAt
  have hCcont : ContinuousAt (fun p => opC ((matrixOperator G).comp R₀)
      ((matrixOperator (Fm 0)).comp S₀) S₀ (matrixOperator (Fm p))) 0 :=
    (hFcont.clm_comp continuousAt_const).add continuousAt_const
  have hCnear : ∀ᶠ p in 𝓝 (0 : ComplexModel d),
      (opC ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
        (matrixOperator (Fm p))).IsInvertible :=
    hCcont (show {T : (Fin a → holSubalgebra K) →L[ℂ] (Fin a → holSubalgebra K) | T.IsInvertible} ∈
      𝓝 (opC ((matrixOperator G).comp R₀) ((matrixOperator (Fm 0)).comp S₀) S₀
        (matrixOperator (Fm 0))) by rw [hC0]; exact isInvertible_mem_nhds_id)
  have hsupp := native_corrected_directExact_near_schur_support d t hKK₀ hO hF hK₀ G₀ hG₀ hex R₀ hR S₀ hS
  have href := corrected_relation_opA_invertible_near_origin
    (show (0 : ComplexModel d) ∈ (univ : Set (ComplexModel d)) from mem_univ _) hFm hex' hR hS'
  filter_upwards [hnear,hCnear,hsupp,href] with p hp hpC hpSupp hpRef
  refine ⟨hpC, fun hpS => ?_⟩
  let Gr := kerFamily Fm G R₀ S₀ 0 p
  have hD : DirectExact Gr (Fm p) := hpSupp hpC hpS
  refine ⟨Gr,hD,hpRef,?_⟩
  intro z hz i l
  have h := congrArg (fun q : holSubalgebra K => (q : C(K,ℂ)) ⟨z,hz⟩) (hD.comp i l)
  simpa [Fm, restrictParam_apply K (hF _ _) hp, extendZero_of_mem K _ hz] using h
end
end Hironaka.Analytic.Unibranch.HironakaG10SameWindowSupportRelation
