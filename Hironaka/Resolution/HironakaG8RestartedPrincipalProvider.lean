import Hironaka.Resolution.HironakaG8RestartedEmptyEpoch
import Hironaka.Resolution.HironakaG8NativePhaseCertificate
import Hironaka.Resolution.HironakaG8PrincipalNativeInitialization
import Hironaka.Resolution.HironakaActualControlledNeighborhoodGenerators
import Hironaka.Resolution.HironakaActualHistoricalInitialAffineDictionary
import Hironaka.Resolution.HironakaActualFixedFlatteningHSComparison
import Hironaka.Resolution.HironakaG1OriginalWeightedMaximalOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8RestartedPrincipalProvider
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  NormalCrossings HironakaEmbeddedAnalytic ResolutionInvariantSpec HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaActualOriginalInitialHSPhase HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualHistoricalHSMarkedDomain HironakaActualHistoricalInitialAffineDictionary
  HironakaG8PrincipalNativeInitialization HironakaG1OriginalWeightedMaximalOrder
  HironakaActualControlledNeighborhoodGenerators HironakaActualFixedFlatteningHSComparison
  HironakaRelativeNormalDeformationInitialRelations HironakaSmoothCentreCoherentDomain
  HironakaSmoothSubmersionGermIdealColon HironakaActualPrescribedCentreRebasing
  HironakaActualOpenEmbeddingVanishingIdeal HomogenizedIdealAlong HironakaG8NativePhaseCertificate

variable {n : ℕ} {X : CMfd.{0} (n+1)}

/-- Nonzero principality of the actual analytic stalk, using a whole germ
generator on the given manifold. This predicate does not select a chart. -/
def NonzeroPrincipalAt (I : GermIdeal (n+1) X) (x : X) : Prop :=
  ∃ f : X → ℂ, HolomorphicAt (n+1) f x ∧ (¬ ∀ᶠ y in 𝓝 x, f y = 0) ∧
    ∀ F, I.mem x F ↔ IsInSpanAt (n := n+1) (· = f) x F

private theorem adaptedGerm_ne_zero_of_nonzero_stalk (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n+1) (chartAt (ComplexModel (n+1)) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel (n+1)) x x) = 0)
    (F : X → ℂ) (hF : HolomorphicAt (n+1) F x) (hn : ¬ ∀ᶠ y in 𝓝 x, F y = 0) :
    adaptedGerm x Φ h0 F hF ≠ 0 := by
  intro hz
  apply hn
  have he : (fun w => F (GiraudAlong.flatInv Φ w)) =ᶠ[𝓝 (0 : ComplexModel (n+1))] (fun _ => 0) := by
    have hz' : adaptedGerm x Φ h0 F hF = HolGerm.mk (fun _ => 0)
        (Eventually.of_forall fun _ => differentiableAt_const (0 : ℂ)) := hz.trans (by rfl)
    exact HolGerm.mk_eq_mk_iff.mp hz'
  have ht : Tendsto (GiraudAlong.flatMap Φ) (𝓝 x) (𝓝 (0 : ComplexModel (n+1))) := by
    have ht := (HomogenizedGlueingAlong.continuousAt_flatMap
      (BlowupFlatCoordinates.mem_flatDomain_self Φ)).tendsto
    simpa only [GiraudAlong.flatMap,h0] using ht
  filter_upwards [ht.eventually he,(BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds
    (BlowupFlatCoordinates.mem_flatDomain_self Φ)] with y hy hyD
  rwa [GiraudAlong.flatInv_flatMap hyD] at hy

/-- Intrinsic principality transfers to the whole origin ideal in whichever
actual centred flattening the native provider constructs. -/
theorem flattened_origin_principal_of_intrinsic (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n+1) W) (x : X)
    (hp : NonzeroPrincipalAt (vanishingIdeal (n := n+1) W) x)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (n+1)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (n+1)) x x) = 0) :
    ∃ g : HolGerm (ComplexModel (n+1)), g ≠ 0 ∧
      originalCoherentOriginIdeal (vanishingIdeal (n := n+1) (actualFixedFlatteningSet x Φ W)) =
        Ideal.span {g} := by
  let I := vanishingIdeal (n := n+1) W
  obtain ⟨f,hf,hn,hGen⟩ := hp
  let g := adaptedGerm x Φ h0 f hf
  refine ⟨g,adaptedGerm_ne_zero_of_nonzero_stalk x Φ h0 f hf hn,?_⟩
  have hFlat := actual_flattened_origin_eq_adapted I (CartanIrreducible.cartanCoherence W hW)
    x Φ h0
  have hx := actualFlattening_target_zero_mem x Φ h0
  have hId : originalCoherentOriginIdeal (actualFlattenedOriginalSheaf I x Φ) =
      originalCoherentOriginIdeal (vanishingIdeal (n := n+1) (actualFixedFlatteningSet x Φ W)) := by
    unfold originalCoherentOriginIdeal
    apply congrArg Ideal.span
    ext F
    constructor
    · rintro ⟨u,hu,hmem,rfl⟩
      exact ⟨u,hu,(flattened_vanishing_mem_iff x Φ hsrc W 0 hx u).mp hmem,rfl⟩
    · rintro ⟨u,hu,hmem,rfl⟩
      exact ⟨u,hu,(flattened_vanishing_mem_iff x Φ hsrc W 0 hx u).mpr hmem,rfl⟩
  rw [← hId,hFlat]
  have h (F : X → ℂ) : I.mem x F ↔ IsInSpanAt (n := n+1) (· ∈ range (fun _ : Unit => f)) x F := by
    simpa only [range_const,mem_singleton_iff] using hGen F
  have hSpan := actual_native_adapted_ideal_of_whole_generation I x Φ h0
    (fun _ : Unit => f) (fun _ => hf) h
  simpa only [range_const] using hSpan

/-- The actual lower Hilbert–Samuel provider initializes on a literal
open in the existing manifold. Intrinsic nonzero principality makes the
native record the whole vanishing sheaf, and the provider gives its
maximal-order mark and genuine Hilbert–Samuel cosupport. -/
theorem exists_principal_native_record_on_literal_open
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (x : X) (hx : x ∈ singularSet (n := n+1) W)
    (hp : NonzeroPrincipalAt (vanishingIdeal (n := n+1) W) x) :
    ∃ (V : Opens X) (hxV : x ∈ V) (q : ℕ),
      let W' := (Subtype.val : V → X) ⁻¹' W
      let Q : MarkedIdeal (n+1) (CMfd.of (n := n+1) V) := ⟨univ,[],vanishingIdeal (n := n+1) W',q⟩
      IsInvDomain (n+1) Q ∧ IsMaximalOrderAlong Q.N Q.ideal q ∧
      (⟨x,hxV⟩ : V) ∈ Q.cosupp ∧
      Q.cosupp = {v | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) W) v.val ℓ =
        hilbertSamuelAt (vanishingIdeal (n := n+1) W) x ℓ} ∧
      Q.cosupp ⊆ (Subtype.val : V → X) ⁻¹' singularSet (n := n+1) W := by
  obtain ⟨Φ,hΦsrc,hΦ0⟩ := NormalCrossings.exists_centred_coordinates (n := n+1) x
  obtain ⟨Ψ,hΨ0,hΞsrc,hΞ0,G,_S,P,hSpan,_hMem,hw,_hPrefix,_hContact,_hJac,hU,hRef,
    V,η,hxV,hη,_hCov,hDom,hCos,hSing,hZero,_hTerminal⟩ :=
    exists_original_initial_hs_phase W hW x hx [] NormalCrossings.isSNCDivisor_nil Φ hΦsrc hΦ0
  let Ξ := currentCoordinateFlattening x Φ hΦ0 Ψ hΨ0
  let W₀ := actualFixedFlatteningSet x Ξ W
  let U := presentationOpen P
  let b : U → X := fun y => (η y : X)
  let Q₀ : MarkedIdeal (n+1) U := initialWeightedRecord P b []
  obtain ⟨g,hg,hI⟩ := flattened_origin_principal_of_intrinsic W hW x hp Ξ hΞsrc hΞ0
  have hSet : (Subtype.val : U → ComplexModel (n+1)) ⁻¹' W₀ = b ⁻¹' W := by
    ext y
    change (y.val ∈ Ξ.target ∧ actualFlatteningInverseMap x Ξ y.val ∈ W) ↔ (η y : X) ∈ W
    rw [hη]
    exact and_iff_right (hU y.property)
  have hIdeal : Q₀.ideal = vanishingIdeal (n := n+1) (b ⁻¹' W) := by
    rw [← hSet]
    exact principal_initialWeightedRecord_ideal P g hg hI hw b
  have hBound : IsMaximalOrderAlong Q₀.N Q₀.ideal Q₀.d :=
    initialWeightedRecord_maximalOrder P hSpan hRef hw b [] hDom
  let Qv : MarkedIdeal (n+1) V :=
    ⟨univ,[],vanishingIdeal (n := n+1) ((Subtype.val : V → X) ⁻¹' W),Q₀.d⟩
  have hInv : ((η.symm : V → U) ⁻¹' (b ⁻¹' W)) = (Subtype.val : V → X) ⁻¹' W := by
    ext y
    change (η (η.symm y) : X) ∈ W ↔ (y : X) ∈ W
    rw [η.apply_symm_apply]
  have hQv : MarkedIdeal.pullback η.symm Q₀ = Qv := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ rfl ?_ rfl
    · exact preimage_univ
    ·
      change GermIdeal.pullback (m := n+1) η.symm Q₀.ideal = Qv.ideal
      rw [hIdeal,pullback_vanishingIdeal_of_biholomorphism,hInv]
  have hDomV := InvDomainTowerAlong.isInvDomain_pullback η.symm hDom
  change IsInvDomain (n+1) (MarkedIdeal.pullback η.symm Q₀) at hDomV
  rw [hQv] at hDomV
  have hCosV : Qv.cosupp = (η.symm : V → U) ⁻¹' Q₀.cosupp := by
    rw [← hQv]
    exact cosupp_pullback η.symm.contMDiff η.contMDiff η.symm_apply_apply η.apply_symm_apply Q₀
      (fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDom.isWellFormed.isCoherent hf)
  let Qhi : MarkedIdeal (n+1) U := {Q₀ with d := Q₀.d+1}
  have hCapV : IsMaximalOrderAlong Qv.N Qv.ideal Qv.d := by
    have hHi := cosupp_pullback η.symm.contMDiff η.contMDiff η.symm_apply_apply η.apply_symm_apply Qhi
      (fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDom.isWellFormed.isCoherent hf)
    intro y hy
    have hy' : y ∈ (MarkedIdeal.pullback η.symm Qhi).cosupp := by
      change y ∈ ({MarkedIdeal.pullback η.symm Q₀ with d := Q₀.d+1}).cosupp
      rwa [hQv]
    rw [hHi] at hy'
    exact hBound (η.symm y) hy'
  have hProfile : Qv.cosupp = {v : V | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) W) v.val ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n+1) W) x ℓ} := by
    rw [hCosV]
    change Q₀.cosupp = _ at hCos
    rw [hCos]
    ext y
    change (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) W) (η (η.symm y) : X) ℓ = _) ↔ _
    rw [η.apply_symm_apply]
    rfl
  refine ⟨V,hxV,Q₀.d,hDomV,hCapV,?_,hProfile,?_⟩
  · rw [hProfile]
    exact fun _ => rfl
  · intro y hy
    have hy₀ : η.symm y ∈ Q₀.cosupp := by
      change y ∈ Qv.cosupp at hy
      rwa [hCosV] at hy
    have hyS := hSing hy₀
    change (η (η.symm y) : X) ∈ singularSet (n := n+1) W at hyS
    rw [η.apply_symm_apply] at hyS
    exact hyS

/-- A genuine higher native phase misses an open with strictly smaller
singular profile. On its literal transformed open the lower phase
provider gives the exact whole top-mark record from intrinsic principality. -/
theorem exists_principal_lower_record_after_actual_higher_phase
    {D : CMfd.{0} (n+1)} (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    {H : ℕ → ℕ} (T : BlowupTower X D) (hPhase : ActualNativePhase W [] H T)
    (O : Opens X)
    (hSmaller : ∀ x ∈ (O : Set X) ∩ singularSet (n := n+1) W,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) W) x) < toLex H)
    (a : openPreimage T O) :
    let U := openPreimage T O
    let B := CMfd.of (n := n+1) U
    let W' := (Subtype.val : U → D) ⁻¹' strictTransform (n+1) T.proj W
    a ∈ singularSet (n := n+1) W' →
    NonzeroPrincipalAt (X := B) (vanishingIdeal (n := n+1) W') a →
    ResolutionInvariantExt.IsEmptyTower (restrict O T) ∧
    ∃ (V : Opens B) (haV : a ∈ V) (q : ℕ),
      let W'' := (Subtype.val : V → B) ⁻¹' W'
      let Q : MarkedIdeal (n+1) (CMfd.of (n := n+1) V) := ⟨univ,[],vanishingIdeal (n := n+1) W'',q⟩
      IsInvDomain (n+1) Q ∧ IsMaximalOrderAlong Q.N Q.ideal q ∧
      (⟨a,haV⟩ : V) ∈ Q.cosupp ∧
      Q.cosupp = {v | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) W') v.val ℓ =
        hilbertSamuelAt (vanishingIdeal (n := n+1) W') a ℓ} ∧
      Q.cosupp ⊆ (Subtype.val : V → B) ⁻¹' singularSet (n := n+1) W' ∧
      ∃ L : Opens (CMfd.of (n := n+1) O), V = openPreimage (restrict O T) L := by
  dsimp only
  intro ha hp
  have hAnalytic := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have he := hPhase.empty_restrict_of_smaller_profile O hSmaller
  let U := openPreimage T O
  let B := CMfd.of (n := n+1) U
  let W' := (Subtype.val : U → D) ⁻¹' strictTransform (n+1) T.proj W
  obtain ⟨V,haV,q,hDom,hCap,hAnchor,hHS,hS⟩ :=
    exists_principal_native_record_on_literal_open (X := B) W'
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hAnalytic U) a ha hp
  obtain ⟨β,hβ⟩ := HironakaOriginalEmptyHeadPrefix.exists_empty_tower_projection (restrict O T) he
  let L : Opens (CMfd.of (n := n+1) O) :=
    ⟨β.symm ⁻¹' (V : Set (openPreimage T O)),V.isOpen.preimage β.symm.continuous⟩
  have hOpen : V = openPreimage (restrict O T) L := by
    ext y
    change y ∈ V ↔ β.symm ((restrict O T).proj y) ∈ V
    rw [← hβ,β.symm_apply_apply]
  exact ⟨he,V,haV,q,hDom,hCap,hAnchor,hHS,hS,L,hOpen⟩

end
end Hironaka.HironakaG8RestartedPrincipalProvider
