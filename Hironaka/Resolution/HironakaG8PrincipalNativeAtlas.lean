import Hironaka.Resolution.HironakaG11PresNativeStateWindow
import Hironaka.Resolution.HironakaG8PrincipalOccupiedRecordProvider
import Hironaka.Resolution.HironakaG8PrincipalEpochLabels
import Hironaka.Resolution.HironakaG8CompactNativeFirstStep

/-! Exact principal chart records certified by the actual native window producer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalNativeAtlas

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualHistoricalInitialFunctionWindow HironakaActualHistoricalNativeFunctionTower
  HironakaActualHistoricalNativeFunctionSuccessor HironakaActualHistoricalNativeGivenTower
  HironakaActualHistoricalNativeStageStep HironakaActualHistoricalSortedPrefixFrames
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualRelativeNormalJetDivision
  HironakaActualFixedInheritedSelector HironakaActualInheritedNestedContactFlag
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaActualInheritedSmallTails HironakaActualWeightedVertexSmallTails
  HironakaActualFiniteDegLexWeights HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain
  HironakaActualPrescribedCentreRebasing HironakaActualFixedFlatteningHSComparison
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance HironakaActualVanishingIntrinsicHSTransport
  HironakaActualCompactHSMaximalProfile HironakaSmoothSubmersionGermIdealColon
  HironakaActualWeightedCoefficientCompression HironakaActualOriginalFormalHSTransfer
  HironakaActualOriginalScaledAnalyticDivision HironakaG11PresTowerState HironakaG11PresLineState
  HironakaG11PresNativePhase
  HironakaEmbeddedAnalytic BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  NormalCrossings HironakaG8RestartedPrincipalProvider HironakaG8PrincipalNativeInitialization
  HironakaActualOpenEmbeddingVanishingIdeal HironakaBaseChange HomogenizedIdealAlong
  HironakaG1OriginalWeightedMaximalOrder GermIdealOrder

variable {m : ℕ}

/-- The actual native-state producer retains the exact principal ideal and its maximal order. -/
private theorem exists_exact_principal_native_state_phase_window
    {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m+1)) M]
    [IsComplexManifold (m+1) M] (W : Set M) (hW : IsComplexAnalyticSubset (n := (m+1)) W)
    (a₀ : M) (ha₀ : a₀ ∈ singularSet (n := (m+1)) W)
    (hp : NonzeroPrincipalAt (X := CMfd.of (n := (m+1)) M) (vanishingIdeal (n := (m+1)) W) a₀) (U₀ : Set M) (hU₀ : IsOpen U₀) (haU₀ : a₀ ∈ U₀) :
    ∃ (U : Opens (ComplexModel (m+1))) (V : Opens M)
      (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel (m+1)), 𝓘(ℂ, ComplexModel (m+1))⟯ V)
      (O : Opens (ComplexModel (m+1))) (hOU : O ≤ U) (z₀ : O)
      (Q : MarkedIdeal (m+1) (CMfd.of (n := (m+1)) (opensIn U O))),
      (η (Opens.inclusion hOU z₀) : M) = a₀ ∧
      (∀ z : O, (η (Opens.inclusion hOU z) : M) ∈ U₀) ∧
      IsInvDomain (m+1) Q ∧ Q.E = [] ∧
      NativeHSState Q ((Subtype.val : opensIn U O → U) ⁻¹' ((fun z : U => (η z : M)) ⁻¹' W))
        (hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a₀) ∧
      Q.ideal = vanishingIdeal (n := (m+1))
        ((Subtype.val : opensIn U O → U) ⁻¹' ((fun z : U => (η z : M)) ⁻¹' W)) ∧
      IsMaximalOrderAlong Q.N Q.ideal Q.d := by
  obtain ⟨Φ, hΦsrc, hΦ0⟩ := NormalCrossings.exists_centred_coordinates (n := (m+1)) a₀
  obtain ⟨Ψ, hΨ0, hΞsrc, hΞ0, G, S, PHS, hSpan, _hMem, hPositive, hRed, hContact, _hJac, hPHS,
    hHS₀, V, η, _haV, hη, hCov, hDom, hCut, _hSing, _hZeroCut⟩ :=
    exists_original_initial_hs_data W hW a₀ ha₀ ([] : List (Set M)) (isSNCDivisor_nil (n := (m+1)))
      Φ hΦsrc hΦ0
  let Ξ := currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
  let Bset := actualFixedFlatteningSet a₀ Ξ W
  let I := originalCoherentOriginIdeal (vanishingIdeal (n := (m+1)) Bset)
  let U₁ := presentationOpen PHS
  let Q₀ := initialWeightedRecord PHS (fun z => (η z : M)) ([] : List (Set M))
  let Wbase := (Subtype.val : U₁ → ComplexModel (m+1)) ⁻¹' Bset
  let fMap : U₁ → M := fun z => (η z : M)
  have hMap : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel (m+1)) ∞ fMap :=
    contMDiff_subtype_val.comp η.contMDiff
  have hSet : Wbase = fMap ⁻¹' W := by
    ext z
    change (z.val ∈ Ξ.target ∧ actualFlatteningInverseMap a₀ Ξ z.val ∈ W) ↔ (η z : M) ∈ W
    rw [hη z]
    exact and_iff_right (hPHS z.property)
  have hWbase : IsComplexAnalyticSubset (n := (m+1)) Wbase := by
    rw [hSet]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hMap hW
  let z₀ : U₁ := ⟨0, PHS.zero_mem⟩
  have hMapZero : fMap z₀ = a₀ := by
    change (η z₀ : M) = a₀
    rw [hη z₀]
    exact actualFlatteningInverseMap_zero a₀ Ξ hΞ0
  obtain ⟨P, s, hs0, _hs, δ, hBound, _hδ, hWinOpen, hWinZero, _hWinSub, hWords, hOwn, hF₀,
    hInitialHistory⟩ :=
    exists_actual_initial_native_original_function_window Bset hSpan PHS S hRed hContact fMap
      ([] : List (Set M))
  let aFull : Fin (historicalDegreePrefixCount (actualVertexWords (m+1) I) P.germs.degreeBound) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I) :=
    (historicalDegreeFullLabelEquiv (actualVertexWords (m+1) I) P.germs.degreeBound hBound).trans
      (actualVertexEnumeration (m+1) I)
  let wFull := historicalDegreePrefixWords (actualVertexWords (m+1) I) P.germs.degreeBound
  let F₀ := fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I))
    (x : U₁) => (s ^ weightedDegree (degLexWeight (m+1) P.germs.degreeBound) v.val)⁻¹ *
      PHS.representatives v x.val
  obtain ⟨Uhs, haUhs, hUpperOriginal, _hLexUpper⟩ := exists_actual_entire_hs_pointwise_upper_window
    (vanishingIdeal (n := (m+1)) W) (CartanIrreducible.cartanCoherence W hW) a₀
  let Allowed : Set U₁ := (Subtype.val : U₁ → ComplexModel (m+1)) ⁻¹' historicalNativeJetWindow P s hs0 δ ∩
    fMap ⁻¹' (Uhs : Set M) ∩ fMap ⁻¹' U₀
  have hAllowedOpen : IsOpen Allowed :=
    ((hWinOpen.preimage continuous_subtype_val).inter (Uhs.isOpen.preimage hMap.continuous)).inter
      (hU₀.preimage hMap.continuous)
  have hAllowedZero : z₀ ∈ Allowed :=
    ⟨⟨hWinZero, by change fMap z₀ ∈ Uhs; rw [hMapZero]; exact haUhs⟩,
      by change fMap z₀ ∈ U₀; rw [hMapZero]; exact haU₀⟩
  let O' : Opens (ComplexModel (m+1)) :=
    ⟨(Subtype.val : U₁ → ComplexModel (m+1)) '' Allowed, U₁.isOpen.isOpenMap_subtype_val _ hAllowedOpen⟩
  have hO'U : O' ≤ U₁ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.property
  let O : Opens U₁ := opensIn U₁ O'
  have hmemO (x : U₁) : x ∈ O ↔ x ∈ Allowed := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hOwindow : ∀ x ∈ O, x.val ∈ historicalNativeJetWindow P s hs0 δ :=
    fun x hx => ((hmemO x).mp hx).1.1
  let Q := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → U₁) Q₀
  let Wphase := (Subtype.val : O → U₁) ⁻¹' Wbase
  let ι : O → M := fun x => (η x.val : M)
  have hDomPhase : IsInvDomain (m+1) Q := InvDomainTowerAlong.isInvDomain_pullback_val O hDom
  have hQI : Q.ideal.IsCoherent := hDomPhase.isWellFormed.isCoherent
  have hQN : Q.N = univ := by
    change (Subtype.val : O → U₁) ⁻¹' univ = univ
    exact preimage_univ
  have hQMark : Q.d = weightedCommonMark
      (fun v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I) =>
        normalExponentDegree v.val) := rfl
  have hQE : Q.E = [] := rfl
  have hWphase : IsComplexAnalyticSubset (n := (m+1)) Wphase :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWbase
  have hHSPhase (x : O) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n := (m+1)) Wphase) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) (ι x) ℓ :=
    (hilbertSamuelAt_vanishing_actual_open_any O Wbase x ℓ).trans
      ((hilbertSamuelAt_vanishing_actual_open_any U₁ Bset x.val ℓ).trans (hCov x.val ℓ))
  have hCutPhase : Q.cosupp = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := (m+1)) Wphase) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a₀ ℓ} := by
    change (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → U₁) Q₀).cosupp = _
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val Q₀
      (fun _ _ hg => holomorphicAt_of_mem_coherent Q₀.ideal hDom.isWellFormed.isCoherent hg) O, hCut]
    ext x
    change (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) (ι x) ℓ =
      hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a₀ ℓ) ↔
        ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := (m+1)) Wphase) x ℓ =
          hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a₀ ℓ
    simp only [hHSPhase]
  have hUpperPhase (x : O) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n := (m+1)) Wphase) x ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a₀ ℓ := by
    rw [hHSPhase]
    exact hUpperOriginal (ι x) ((hmemO x.val).mp x.property).1.2 ℓ
  have hAnchored (x : O) (hx : x ∈ Q.cosupp) :
      ActualHistoricalNativeFunctionPresentation S aFull wFull Wphase Q F₀ hF₀
        (Subtype.val : O → U₁) contMDiff_subtype_val x := by
    have hProfilePhase : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := (m+1)) Wphase) x ℓ =
        hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a₀ ℓ := by
      rw [hCutPhase] at hx
      exact hx
    have hProfileBase : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := (m+1)) Wbase) x.val ℓ =
        hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a₀ ℓ := fun ℓ =>
      (hilbertSamuelAt_vanishing_actual_open_any O Wbase x ℓ).symm.trans (hProfilePhase ℓ)
    have hAtBase := hInitialHistory x.val (hOwindow x.val x.property) hProfileBase
    exact actual_native_original_function_open_restriction S aFull wFull Wbase
      (CartanIrreducible.cartanCoherence Wbase hWbase) Q₀ hDom.isWellFormed.isCoherent O x
        F₀ hF₀ id contMDiff_id hAtBase
  have hPoint (x : O) (hx : x ∈ Q.cosupp) :
      ActualHistoricalNativePointPresentation S aFull wFull Wphase Q x := by
    obtain ⟨Θ, hΘsrc, hΘ0, Γ, _d, hFive, hSpanAt, hCompAt, _hd, _hEq⟩ := hAnchored x hx
    exact ⟨Θ, hΘsrc, hΘ0, Γ, hFive, hSpanAt, hCompAt⟩
  have hState : NativeHSState (X := CMfd.of (n := (m+1)) O) Q Wphase
      (hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a₀) :=
    ⟨⟨(m+1), CMfd.of (n := (m+1)) M, W, a₀, hW, ha₀, rfl⟩, hWphase, hQN, hQI, _, S, _, aFull, wFull, hWords, hPositive, hOwn,
      hQMark, hCutPhase, hUpperPhase, hPoint⟩
  obtain ⟨g,hg,hI⟩ := flattened_origin_principal_of_intrinsic (X := CMfd.of (n := (m+1)) M)
    W hW a₀ hp Ξ hΞsrc hΞ0
  have hIdeal₀ : Q₀.ideal = vanishingIdeal (n := (m+1)) Wbase :=
    principal_initialWeightedRecord_ideal PHS g hg hI hPositive fMap
  have hIdeal : Q.ideal = vanishingIdeal (n := (m+1)) Wphase := by
    change GermIdeal.pullback (m := (m+1)) (Subtype.val : O → U₁) Q₀.ideal = _
    rw [hIdeal₀]
    exact pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val O) Wbase
  have hMax₀ : IsMaximalOrderAlong Q₀.N Q₀.ideal Q₀.d :=
    initialWeightedRecord_maximalOrder PHS hSpan hHS₀ hPositive fMap [] hDom
  have hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d := by
    intro x hx
    let B : MarkedIdeal (m+1) U₁ := {Q₀ with d := Q₀.d+1}
    have hx' : x ∈ (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → U₁) B).cosupp := hx
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val B
      (fun _ _ hg => holomorphicAt_of_mem_coherent Q₀.ideal hDom.isWellFormed.isCoherent hg) O] at hx'
    exact hMax₀ x.val hx'
  have hz₀O : (z₀ : ComplexModel (m+1)) ∈ O' := ⟨z₀, hAllowedZero, rfl⟩
  refine ⟨U₁, V, η, O', hO'U, ⟨z₀.val, hz₀O⟩, Q, hMapZero, fun z => ?_, hDomPhase, hQE, ?_⟩
  · have hz : Opens.inclusion hO'U z ∈ O := z.property
    exact ((hmemO _).mp hz).2
  · have hWeq : Wphase = (Subtype.val : opensIn U₁ O' → U₁) ⁻¹' ((fun z : U₁ => (η z : M)) ⁻¹' W) := by
      change (Subtype.val : O → U₁) ⁻¹' Wbase = _
      rw [hSet]
    rw [← hWeq]
    exact ⟨hState,hIdeal,hMax⟩



open MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG8OpenHoloEmbeddingComposition HironakaG8NativeBoundaryComparison

variable {X : CMfd.{0} (m+1)}

private theorem exists_exact_principal_native_state_on_ambient_open
    (W : Set X) (hW : IsComplexAnalyticSubset (n := (m+1)) W)
    (a : X) (ha : a ∈ singularSet (n := (m+1)) W)
    (hp : NonzeroPrincipalAt (vanishingIdeal (n := (m+1)) W) a) (U₀ : Opens X) (haU : a ∈ U₀) :
    ∃ (D : Opens X), a ∈ D ∧ (D : Set X) ⊆ U₀ ∧
      ∃ (P : MarkedIdeal (m+1) (CMfd.of (n := (m+1)) D)), IsInvDomain (m+1) P ∧ P.E = [] ∧
        NativeHSState P ((Subtype.val : D → X) ⁻¹' W)
          (hilbertSamuelAt (vanishingIdeal (n := (m+1)) W) a) ∧
        P.ideal = vanishingIdeal (n := (m+1)) ((Subtype.val : D → X) ⁻¹' W) ∧
        IsMaximalOrderAlong P.N P.ideal P.d := by
  obtain ⟨U, V, η, O, hOU, z, Q, hz, hInside, hQ, hQE, hState, hI, hMax⟩ :=
    exists_exact_principal_native_state_phase_window W hW a ha hp U₀ U₀.isOpen haU
  let f : opensIn U O → X := fun x => (η x.val : X)
  have hf : IsOpenHoloEmbedding (m+1) f :=
    isOpenHoloEmbedding_comp (A := X) (B := CMfd.of (n := (m+1)) U) (C := CMfd.of (n := (m+1)) (opensIn U O))
      (⟨V, η, fun _ => rfl⟩ : IsOpenHoloEmbedding (m+1) (fun x : U => (η x : X)))
      (isOpenHoloEmbedding_val (opensIn U O))
  obtain ⟨D, e, he⟩ := hf
  let z₁ : opensIn U O := ⟨Opens.inclusion hOU z, z.property⟩
  have hfa : f z₁ = a := hz
  have haD : a ∈ D := by
    rw [← hfa, he]
    exact (e z₁).property
  have hDU : (D : Set X) ⊆ U₀ := by
    intro x hx
    let y := e.symm ⟨x, hx⟩
    have hfy : f y = x := by rw [he, e.apply_symm_apply]
    rw [← hfy]
    exact hInside ⟨(y.val : U).val, y.property⟩
  let P := MarkedIdeal.pullback e.symm Q
  have hP : IsInvDomain (m+1) P := InvDomainTowerAlong.isInvDomain_pullback e.symm hQ
  have hPE : P.E = [] := by
    change Q.E.map (e.symm ⁻¹' ·) = []
    rw [hQE]
    rfl
  have hSet : e.symm ⁻¹' (f ⁻¹' W) = (Subtype.val : D → X) ⁻¹' W := by
    ext x
    change f (e.symm x) ∈ W ↔ x.val ∈ W
    rw [he, e.apply_symm_apply]
  have hPIdeal : P.ideal = vanishingIdeal (n := (m+1)) ((Subtype.val : D → X) ⁻¹' W) := by
    change GermIdeal.pullback (m := (m+1)) e.symm Q.ideal = _
    rw [hI, pullback_vanishingIdeal_of_biholomorphism]
    exact congrArg (vanishingIdeal (n := (m+1))) hSet
  have hCap : IsMaximalOrderAlong P.N P.ideal P.d := by
    let Qhi : MarkedIdeal (m+1) (opensIn U O) := {Q with d := Q.d+1}
    intro x hx
    have hx' : x ∈ (MarkedIdeal.pullback e.symm Qhi).cosupp := hx
    rw [cosupp_pullback e.symm.contMDiff e.contMDiff e.symm_apply_apply e.apply_symm_apply Qhi
      (fun _ _ hg => holomorphicAt_of_mem_coherent Q.ideal hQ.isWellFormed.isCoherent hg)] at hx'
    exact hMax (e.symm x) hx'
  refine ⟨D, haD, hDU, P, hP, hPE, ?_, hPIdeal, hCap⟩
  rw [← hSet]
  exact NativeHSState.pullback (X := CMfd.of (n := (m+1)) (opensIn U O))
    (X' := CMfd.of (n := (m+1)) D) e.symm hState


open MarkedIdealRestrictOpen NormalCrossingsInvariance HironakaG8NativeRelativeClearing
  HironakaG8NativePhaseCertificate HironakaG8PrincipalEpochLabels

private abbrev whole (W : Set X) (E : List (Set X)) (q : ℕ) : MarkedIdeal (m+1) X :=
  ⟨univ,E,vanishingIdeal (n := m+1) W,q⟩

private theorem whole_pullback (D : Opens X) (W : Set X) (E : List (Set X)) (q : ℕ) :
    MarkedIdeal.pullback (Subtype.val : D → X) (whole W E q) =
      whole (X := CMfd.of (n := m+1) D) ((Subtype.val : D → X) ⁻¹' W) (E.map ((Subtype.val : D → X) ⁻¹' ·)) q := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl ?_ rfl
  exact pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val D) W

/-- A principal singular point admits an exact whole native-state chart,
with the original mark given by the ordinary order and with all inherited slots. -/
theorem exact_native_chart_of_principal_singular
    (W : Set X) (hW : IsComplexAnalyticSubset (n := m+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m+1) E)
    (hI : (vanishingIdeal (n := m+1) W).IsInvertible)
    (a : X) (ha : a ∈ singularSet (n := m+1) W) (q : ℕ)
    (hOrd : order (m+1) univ (vanishingIdeal (n := m+1) W) a = q)
    (U : Opens X) (haU : a ∈ U) :
    ∃ (D : Opens X), a ∈ D ∧ D ≤ U ∧
      let G := MarkedIdeal.pullback (Subtype.val : D → X) (whole W E q)
      IsInvDomain (m+1) G ∧
      NativeHSState (X := CMfd.of (n := m+1) D) G ((Subtype.val : D → X) ⁻¹' W)
        (hilbertSamuelAt (vanishingIdeal (n := m+1) W) a) := by
  have hp : NonzeroPrincipalAt (vanishingIdeal (n := m+1) W) a := by
    obtain ⟨V,hV,haV,f,hf,hNonzero,hGen⟩ := hI a
    refine ⟨f,InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hf haV,?_,hGen a haV⟩
    intro hZero
    obtain ⟨O,hO,hOpen,haO⟩ := mem_nhds_iff.mp (hZero.and (hV.mem_nhds haV))
    obtain ⟨y,hy,hfy⟩ := hNonzero O hOpen (fun z hz => (hO hz).2) ⟨a,haO⟩
    exact hfy (hO hy).1
  obtain ⟨D,haD,hDU,P,hP,_hNil,hState,hId,hCap⟩ :=
    exists_exact_principal_native_state_on_ambient_open W hW a ha hp U haU
  have hPN : P.N = univ := hState.2.2.1
  let E' := E.map ((Subtype.val : D → X) ⁻¹' ·)
  have hE' : IsSNCDivisor (m+1) E' :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val D) continuous_subtype_val hE
  obtain ⟨hPD,hSD,_⟩ := native_state_with_snc_boundary P hP hState E' hE'
  have hAnchor : (⟨a,haD⟩ : D) ∈ P.cosupp := by
    rw [hState.cosupp_eq]
    exact hilbertSamuelAt_vanishing_actual_open_any D W ⟨a,haD⟩
  have hCos (r : ℕ) : (⟨a,haD⟩ : D) ∈ ({P with d := r} : MarkedIdeal (m+1) D).cosupp ↔
      (r : ℕ∞) ≤ order (m+1) univ (vanishingIdeal (n := m+1) W) a := by
    have hEq : {P with d := r} = MarkedIdeal.pullback (Subtype.val : D → X) (whole W [] r) := by
      rw [whole_pullback]
      exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hPN _hNil hId rfl
    rw [hEq,cosupp_pullback_val (whole W [] r) (fun _ _ hg => hg.1) D]
    rw [le_order_iff (𝔞 := vanishingIdeal (n := m+1) W) (fun _ hg => hg.1)]
    exact ⟨And.right,fun h => ⟨mem_univ a,h⟩⟩
  have hMark : P.d = q := by
    have hLo := (hCos P.d).1 hAnchor
    have hHi : ¬ ((P.d+1 : ℕ) : ℕ∞) ≤ order (m+1) univ (vanishingIdeal (n := m+1) W) a :=
      fun h => hCap ⟨a,haD⟩ ((hCos (P.d+1)).2 h)
    rw [hOrd] at hLo hHi
    have hLe : P.d ≤ q := by exact_mod_cast hLo
    have hNot : ¬ P.d+1 ≤ q := by exact_mod_cast hHi
    omega
  have hFinal : {P with E := E'} = MarkedIdeal.pullback (Subtype.val : D → X) (whole W E q) := by
    rw [whole_pullback]
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hPN rfl hId hMark
  exact ⟨D,haD,hDU,hFinal ▸ hPD,hFinal ▸ hSD⟩


/-- Every point of the genuine supported level has an exact native chart
of the same whole record. All powers can be taken to be one. -/
theorem exists_exact_principal_native_windows
    (W : Set X) (hW : IsComplexAnalyticSubset (n := m+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m+1) E)
    (hI : (vanishingIdeal (n := m+1) W).IsInvertible)
    (a : X) (q : ℕ) (H : ℕ → ℕ)
    (ha : hilbertSamuelAt (vanishingIdeal (n := m+1) W) a = H)
    (hOrd : order (m+1) univ (vanishingIdeal (n := m+1) W) a = q)
    (hSing : phaseLevel W H ⊆ singularSet (n := m+1) W) :
    ∃ A : NativeWindows X (phaseLevel W H) W E H (phaseLevel W H),
      (∀ i, A.record i = MarkedIdeal.pullback (Subtype.val : A.openSet i → X) (whole W E q)) ∧
      (∀ i, A.exponent i = 1) := by
  classical
  let F := whole W E q
  have hChart (i : phaseLevel W H) :
      ∃ (D : Opens X), i.val ∈ D ∧
        IsInvDomain (m+1) (MarkedIdeal.pullback (Subtype.val : D → X) F) ∧
        NativeHSState (X := CMfd.of (n := m+1) D)
          (MarkedIdeal.pullback (Subtype.val : D → X) F) ((Subtype.val : D → X) ⁻¹' W) H := by
    have hi : hilbertSamuelAt (vanishingIdeal (n := m+1) W) i.val = H := i.property
    have hEq : order (m+1) univ (vanishingIdeal (n := m+1) W) i.val = q := by
      rw [← hOrd]
      apply le_antisymm <;> apply le_of_not_gt <;> intro hlt
      · have hh := (principal_profile_lt_iff_order_lt _ _ hI hI a i.val).2 hlt
        rw [ha,hi] at hh
        exact (lt_irrefl _ hh)
      · have hh := (principal_profile_lt_iff_order_lt _ _ hI hI i.val a).2 hlt
        rw [hi,ha] at hh
        exact (lt_irrefl _ hh)
    obtain ⟨D,hiD,_,hD,hN⟩ :=
      exact_native_chart_of_principal_singular W hW E hE hI i.val (hSing i.property) q hEq ⊤ (by simp)
    exact ⟨D,hiD,hD,hi ▸ hN⟩
  choose D hPoint hDomain hNative using hChart
  let A : NativeWindows X (phaseLevel W H) W E H (phaseLevel W H) :=
    { openSet := D
      record := fun i => MarkedIdeal.pullback (Subtype.val : D i → X) F
      domain := hDomain
      native := hNative
      boundary := fun _ => rfl
      exponent := fun _ => 1
      positive := fun _ => le_rfl
      mark := q
      commonMark := fun _ => by change q * 1 = q; simp
      covers := fun x hx => ⟨⟨x,hx⟩, hPoint ⟨x,hx⟩⟩ }
  exact ⟨A,fun _ => rfl,fun _ => rfl⟩

end
end Hironaka.HironakaG8PrincipalNativeAtlas
