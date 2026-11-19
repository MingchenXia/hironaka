import Hironaka.Resolution.HironakaG1ProperNormalNativeCut
import Hironaka.Resolution.HironakaG1ProperNormalNativeChart
import Hironaka.Resolution.HironakaG1ClosedNormalNativeState
import Hironaka.Resolution.HironakaActualIntrinsicStableIdealSquare

/-! The whole analytic zero-graph ideal and the actual native padded state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ProperNormalNativeState
noncomputable section

open HolGerm Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualOpenZeroSectionDifferentials HironakaActualCentreJointJets
  HironakaRelativeNormalIdeal HironakaActualIntrinsicStableIdealSquare
  HironakaActualRelativeNormalGeometry HironakaActualZeroCoordinateContactSeed
  HironakaActualGraphFunctionalIdeal HironakaHolomorphicJetMonomialSpan
  HironakaSmoothSubmersionGermIdealColon HironakaActualWeightedNormalAmbientDerivatives
  HironakaActualCoherentWeightedCoefficientMarked InvertibleIdealQuotient RestrictedIdealExtension
  HironakaActualWeightedNormalPadding IdealOrderArithmetic RelativePrincipalizationSpan
  GermIdealPullbackCalculus BlowupRestrictOpen HironakaG1ProperNormalNativeCut
  HironakaG1ProperNormalNativeChart HironakaG1ClosedNormalNativeState
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG11PresLineState BlowupTowers MarkedIdeals ResolutionInvariantSpec

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem proj_zero (x : U) : projection U (zeroSection U x) = x :=
  Subtype.ext (tangentProjection_tangentInclusion n 1 x.val)

private theorem normal_coordinate_eval (z : productOpen U) :
    relativeNormalCoordinate U z = actualJointNormalProjection n 1 z.val 0 := by
  simp only [relativeNormalCoordinate, Function.comp_apply, addedCoordinate, graphFunction,
    zeroFunction, WithLp.ofLp_zero, Pi.zero_apply, sub_zero]
  rfl

private theorem relative_eq_pullback_zero {W : Set U} :
    liftedCarrier W = (Subtype.val : productOpen U → ComplexModel (n+1)) ⁻¹'
      zeroCoordinateCarrier (m := 1) ((Subtype.val : U → ComplexModel n) '' W) := by
  ext z
  change (projection U z ∈ W ∧ _) ↔
    ((tangentProjection n 1 z.val) ∈ (Subtype.val : U → ComplexModel n) '' W ∧ _)
  refine and_congr_left (fun _ => ?_)
  constructor
  · intro hz
    exact ⟨projection U z,hz,rfl⟩
  · rintro ⟨x,hx,he⟩
    exact (Subtype.ext he : x = projection U z) ▸ hx

/-- On every actual zero section point, the whole ambient vanishing ideal
is the base vanishing ideal extended by the literal linear normal equation. -/
theorem liftedCarrier_vanishing_mem_iff {W : Set U}
    (hW : IsComplexAnalyticSubset (n := n) W)
    (x : U) (F : productOpen U → ℂ) :
    (vanishingIdeal (n := n+1) (liftedCarrier W)).mem (zeroSection U x) F ↔
      (normalPaddingIdeal (vanishingIdeal (n := n) W) 1).mem (zeroSection U x) F := by
  let Wabs := (Subtype.val : U → ComplexModel n) '' W
  let A := vanishingIdeal (n := n) W
  let B := vanishingIdeal (n := n+1) (liftedCarrier W)
  let y := zeroSection U x
  let L := GermIdeal.pullback (m := n+1) (projection U) A
  let K := finiteFunctionIdeal (n := n+1) (fun _ : Unit => fun z => relativeNormalCoordinate U z ^ 1)
  have hWpre : (Subtype.val : U → ComplexModel n) ⁻¹' Wabs = W := by
    simp only [Wabs, preimage_image_eq _ Subtype.val_injective]
  have hKhol : HolomorphicAt (n+1) (fun z => relativeNormalCoordinate U z ^ 1) y :=
    Eventually.of_forall ((normalCoordinate_mdifferentiable U).pow 1)
  have hP : ∀ᶠ z in 𝓝 y, ContMDiffAt
      𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ComplexModel n) ∞ (projection U) z :=
    Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt
  change B.mem y F ↔ (sumIdeal L K).mem y F
  rw [mem_sumIdeal_iff]
  constructor
  · intro hF
    change (vanishingIdeal (n := n+1) (liftedCarrier W)).mem y F at hF
    rw [relative_eq_pullback_zero] at hF
    have hg : (vanishingIdeal (n := n+1) (zeroCoordinateCarrier (m := 1) Wabs)).mem
        (tangentInclusion n 1 x.val) (extendOpens (productOpen U) F) :=
      (vanishingIdeal_opens_mem_iff (productOpen U)).mp hF
    have hs := (zero_coordinate_functional_mem_iff (m := 1) Wabs x.val _).mp hg
    have hs' := isInSpanAt_comp (contMDiff_subtype_val (U := productOpen U)) (y := y) hs
    have he : extendOpens (productOpen U) F ∘ (Subtype.val : productOpen U → ComplexModel (n+1)) = F :=
      funext fun z => extendOpens_val _ _ z
    rw [he] at hs'
    apply hs'.mono
    rintro s ⟨_,(⟨a,ha,rfl⟩ | ⟨i,rfl⟩),rfl⟩
    · left
      have ha' := vanishingIdeal_opens_mem_comp_val U ha
      rw [hWpre] at ha'
      have hHol : HolomorphicAt n (a ∘ Subtype.val) x := ha'.1
      change (GermIdeal.pullback (m := n+1) (projection U) A).mem y ((a ∘ Subtype.val) ∘ projection U)
      rw [← proj_zero x] at ha' hHol
      exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨_,ha',rfl⟩ (hHol.comp_contMDiff hP))
    · right
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have heq : ((fun z : ComplexModel (n+1) => z ((0 : Fin 1).natAdd n)) ∘
          (Subtype.val : productOpen U → ComplexModel (n+1))) =
          fun z => relativeNormalCoordinate U z ^ 1 := by
        funext z
        rw [pow_one, normal_coordinate_eval]
        rfl
      rw [heq]
      exact isInSpanAt_self ⟨(),rfl⟩ hKhol
  · intro hF
    apply GermIdealTotalTransform.mem_of_isInSpanAt_mem
      (CartanIrreducible.cartanCoherence _ (liftedCarrier_isAnalytic hW))
    refine hF.mono ?_
    intro g hg
    rcases hg with hL | hK
    · apply GermIdealTotalTransform.mem_of_isInSpanAt_mem
        (CartanIrreducible.cartanCoherence _ (liftedCarrier_isAnalytic hW))
      refine (GermIdeal.mem_pullback_iff.mp hL).mono ?_
      rintro _ ⟨a,ha,rfl⟩
      refine ⟨ha.1.comp_contMDiff hP, ?_⟩
      filter_upwards [(projection_contMDiff U).continuous.continuousAt.eventually ha.2] with z hz hzW
      exact hz hzW.1
    · apply GermIdealTotalTransform.mem_of_isInSpanAt_mem
        (CartanIrreducible.cartanCoherence _ (liftedCarrier_isAnalytic hW))
      refine hK.mono ?_
      rintro _ ⟨_,rfl⟩
      refine ⟨hKhol, Eventually.of_forall fun z hz => ?_⟩
      change relativeNormalCoordinate U z ^ 1 = 0
      rw [pow_one, normal_coordinate_eval, hz.2]
      rfl

/-- The actual zero-section chart provides both exact whole-ideal identities
for the existing literal padded marked ideal. -/
theorem properNormalMarked_closedNormalAdaptedChart {W : Set U} {Q : MarkedIdeal n U}
    (hW : IsComplexAnalyticSubset (n := n) W) (hQI : Q.ideal.IsCoherent)
    (x : U) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    ClosedNormalAdaptedChart (X := CMfd.of (n := n) U)
      (Y := CMfd.of (n := n+1) (productOpen U))
      (W := W) (D := liftedCarrier W) (P := Q) (Q := properNormalMarked Q) x (zeroSection U x) Φ h0 := by
  let Ψ := productFlat U x Φ
  let hΨ := productFlat_center x Φ h0
  refine ⟨Ψ,productFlat_source_subset x Φ hSrc,hΨ,?_,?_⟩
  · have hSame : adaptedIdeal (vanishingIdeal (n := n+1) (liftedCarrier W)) (zeroSection U x) Ψ hΨ =
        adaptedIdeal (normalPaddingIdeal (vanishingIdeal (n := n) W) 1) (zeroSection U x) Ψ hΨ := by
      unfold adaptedIdeal
      congr 1
      ext g
      constructor
      · rintro ⟨f,hf,hmem,rfl⟩
        exact ⟨f,hf,(liftedCarrier_vanishing_mem_iff hW x f).mp hmem,rfl⟩
      · rintro ⟨f,hf,hmem,rfl⟩
        exact ⟨f,hf,(liftedCarrier_vanishing_mem_iff hW x f).mpr hmem,rfl⟩
    rw [hSame, adaptedIdeal_productFlat_normalPadding _ (CartanIrreducible.cartanCoherence W hW)
      x Φ hSrc h0, pow_one]
  · exact adaptedIdeal_productFlat_normalPadding Q.ideal hQI x Φ hSrc h0 Q.d

/-- The actual whole normal padded record of an original full native state
is itself native for the closed zero graph, with its unchanged mark and
pulled ordered boundary. -/
theorem properNormalMarked_nativeHSState {W : Set U} {Q : MarkedIdeal n U} (H : ℕ → ℕ)
    (hQ : NativeHSState (X := CMfd.of (n := n) U) Q W H) (hDomain : IsInvDomain n Q) :
    NativeHSState (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) (liftedCarrier W) H := by
  obtain ⟨hCut,hUpper⟩ := properNormalMarked_native_cut_and_bound H hQ hDomain
  have hW := hQ.2.1
  have hN := hQ.2.2.1
  have hI := hQ.2.2.2.1
  have hPad := properNormalMarked_isInvDomain Q hDomain
  refine nativeHSState_closedNormal H hQ (liftedCarrier_isAnalytic hW) ?_
    hPad.isWellFormed.isCoherent rfl hCut hUpper ?_
  · change projection U ⁻¹' Q.N = univ
    rw [hN, preimage_univ]
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (properNormalMarked_cosupp Q hDomain).le hz
    exact ⟨x,hx,fun Φ hSrc h0 => properNormalMarked_closedNormalAdaptedChart hW hI x Φ hSrc h0⟩

#print axioms liftedCarrier_vanishing_mem_iff
#print axioms properNormalMarked_nativeHSState

end
end Hironaka.HironakaG1ProperNormalNativeState
