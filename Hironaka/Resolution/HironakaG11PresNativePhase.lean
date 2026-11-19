import Hironaka.Resolution.HironakaG11PresTowerState
import Hironaka.Resolution.HironakaActualHistoricalOriginalNativePhase

/-!
# Native Hilbert–Samuel phase windows inside prescribed neighbourhoods (goal G11, step (3a))

At a singular point `a₀` of a closed analytic subset `W` of a complex manifold `M`, inside ANY
prescribed open neighbourhood `U₀` of `a₀`, the library's native Hilbert–Samuel phase
(`HironakaActualHistoricalOriginalNativePhase`, Hironaka's standard-basis presentation of the
Hilbert–Samuel function with Bennett's properties) gives a window: an open `O ⊆ U ⊆ ℂ^n` of the
presentation open `U ≅ V ⊆ M`, mapped into `U₀`, through `a₀`, with a record `Q` (empty boundary,
whole carrier, in the domain of the invariant of dimension `n`) which presents the Hilbert–Samuel
function `H_{W,a₀}` along all multiple test blow-ups (`HSTowerState`).

* `opensIn U O` (an open `O ⊆ U` of `ℂ^n` as an open subset of the manifold `U`);
* **`exists_native_hs_phase_window`**.

The proof is that of `exists_actual_original_native_anchored_hs_phase` (same producers), with the
phase open chosen inside the extra neighbourhood and the conclusion stated as `HSTowerState`.
Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-tower-state.tex`.
-/

set_option autoImplicit false

open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11PresNativePhase

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
  HironakaActualOriginalScaledAnalyticDivision HironakaG11PresTowerState
  HironakaEmbeddedAnalytic BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  NormalCrossings

variable {n : ℕ}

/-- An open `O ⊆ U` of `ℂ^n` as an open subset of the manifold `U`. -/
def opensIn (U O : Opens (ComplexModel n)) : Opens U :=
  ⟨Subtype.val ⁻¹' (O : Set (ComplexModel n)), O.isOpen.preimage continuous_subtype_val⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A native Hilbert–Samuel window inside a prescribed neighbourhood.** At a singular point `a₀` of
a closed analytic `W ⊆ M` and for any open `U₀ ∋ a₀`, there are an open `U ⊆ ℂ^n`, a biholomorphism
`η : U ≅ V` onto an open `V ⊆ M`, an open `O ⊆ U` containing a point `z₀` over `a₀` and mapped into
`U₀`, and a record `Q` on `O` (empty boundary, carrier `O`, in the domain of the invariant of
dimension `n`) presenting the Hilbert–Samuel function `H_{W,a₀}` on `O ∩ η⁻¹ W` along all multiple
test blow-ups. -/
theorem exists_native_hs_phase_window (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    (a₀ : M) (ha₀ : a₀ ∈ singularSet (n := n) W) (U₀ : Set M) (hU₀ : IsOpen U₀) (haU₀ : a₀ ∈ U₀) :
    ∃ (U : Opens (ComplexModel n)) (V : Opens M)
      (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
      (O : Opens (ComplexModel n)) (hOU : O ≤ U) (z₀ : O)
      (Q : MarkedIdeal n (CMfd.of (n := n) (opensIn U O))),
      (η (Opens.inclusion hOU z₀) : M) = a₀ ∧
      (∀ z : O, (η (Opens.inclusion hOU z) : M) ∈ U₀) ∧
      IsInvDomain n Q ∧ Q.N = univ ∧ Q.E = [] ∧
      HSTowerState Q ((Subtype.val : opensIn U O → U) ⁻¹' ((fun z : U => (η z : M)) ⁻¹' W))
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a₀) := by
  obtain ⟨Φ, hΦsrc, hΦ0⟩ := NormalCrossings.exists_centred_coordinates (n := n) a₀
  obtain ⟨Ψ, hΨ0, _hΞsrc, hΞ0, G, S, PHS, hSpan, _hMem, hPositive, hRed, hContact, _hJac, hPHS,
    _hHS₀, V, η, _haV, hη, hCov, hDom, hCut, _hSing, _hZeroCut, _hPhases⟩ :=
    exists_original_initial_hs_phase W hW a₀ ha₀ ([] : List (Set M)) (isSNCDivisor_nil (n := n))
      Φ hΦsrc hΦ0
  let Ξ := currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
  let Bset := actualFixedFlatteningSet a₀ Ξ W
  let I := originalCoherentOriginIdeal (vanishingIdeal (n := n) Bset)
  let U₁ := presentationOpen PHS
  let Q₀ := initialWeightedRecord PHS (fun z => (η z : M)) ([] : List (Set M))
  let Wbase := (Subtype.val : U₁ → ComplexModel n) ⁻¹' Bset
  let fMap : U₁ → M := fun z => (η z : M)
  have hMap : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ fMap :=
    contMDiff_subtype_val.comp η.contMDiff
  have hSet : Wbase = fMap ⁻¹' W := by
    ext z
    change (z.val ∈ Ξ.target ∧ actualFlatteningInverseMap a₀ Ξ z.val ∈ W) ↔ (η z : M) ∈ W
    rw [hη z]
    exact and_iff_right (hPHS z.property)
  have hWbase : IsComplexAnalyticSubset (n := n) Wbase := by
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
  let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) :=
    (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
      (actualVertexEnumeration n I)
  let wFull := historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
  let F₀ := fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
    (x : U₁) => (s ^ weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹ *
      PHS.representatives v x.val
  obtain ⟨Uhs, haUhs, hUpperOriginal, _hLexUpper⟩ := exists_actual_entire_hs_pointwise_upper_window
    (vanishingIdeal (n := n) W) (CartanIrreducible.cartanCoherence W hW) a₀
  let Allowed : Set U₁ := (Subtype.val : U₁ → ComplexModel n) ⁻¹' historicalNativeJetWindow P s hs0 δ ∩
    fMap ⁻¹' (Uhs : Set M) ∩ fMap ⁻¹' U₀
  have hAllowedOpen : IsOpen Allowed :=
    ((hWinOpen.preimage continuous_subtype_val).inter (Uhs.isOpen.preimage hMap.continuous)).inter
      (hU₀.preimage hMap.continuous)
  have hAllowedZero : z₀ ∈ Allowed :=
    ⟨⟨hWinZero, by change fMap z₀ ∈ Uhs; rw [hMapZero]; exact haUhs⟩,
      by change fMap z₀ ∈ U₀; rw [hMapZero]; exact haU₀⟩
  let O' : Opens (ComplexModel n) :=
    ⟨(Subtype.val : U₁ → ComplexModel n) '' Allowed, U₁.isOpen.isOpenMap_subtype_val _ hAllowedOpen⟩
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
  have hDomPhase : IsInvDomain n Q := InvDomainTowerAlong.isInvDomain_pullback_val O hDom
  have hQI : Q.ideal.IsCoherent := hDomPhase.isWellFormed.isCoherent
  have hQN : Q.N = univ := by
    change (Subtype.val : O → U₁) ⁻¹' univ = univ
    exact preimage_univ
  have hQMark : Q.d = weightedCommonMark
      (fun v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) =>
        normalExponentDegree v.val) := rfl
  have hQE : Q.E = [] := rfl
  have hWphase : IsComplexAnalyticSubset (n := n) Wphase :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWbase
  have hHSPhase (x : O) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n := n) Wphase) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) (ι x) ℓ :=
    (hilbertSamuelAt_vanishing_actual_open_any O Wbase x ℓ).trans
      ((hilbertSamuelAt_vanishing_actual_open_any U₁ Bset x.val ℓ).trans (hCov x.val ℓ))
  have hCutPhase : Q.cosupp = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) Wphase) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) a₀ ℓ} := by
    change (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → U₁) Q₀).cosupp = _
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val Q₀
      (fun _ _ hg => holomorphicAt_of_mem_coherent Q₀.ideal hDom.isWellFormed.isCoherent hg) O, hCut]
    ext x
    change (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) (ι x) ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) a₀ ℓ) ↔
        ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) Wphase) x ℓ =
          hilbertSamuelAt (vanishingIdeal (n := n) W) a₀ ℓ
    simp only [hHSPhase]
  have hUpperPhase (x : O) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n := n) Wphase) x ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n) W) a₀ ℓ := by
    rw [hHSPhase]
    exact hUpperOriginal (ι x) ((hmemO x.val).mp x.property).1.2 ℓ
  have hAnchored (x : O) (hx : x ∈ Q.cosupp) :
      ActualHistoricalNativeFunctionPresentation S aFull wFull Wphase Q F₀ hF₀
        (Subtype.val : O → U₁) contMDiff_subtype_val x := by
    have hProfilePhase : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) Wphase) x ℓ =
        hilbertSamuelAt (vanishingIdeal (n := n) W) a₀ ℓ := by
      rw [hCutPhase] at hx
      exact hx
    have hProfileBase : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) Wbase) x.val ℓ =
        hilbertSamuelAt (vanishingIdeal (n := n) W) a₀ ℓ := fun ℓ =>
      (hilbertSamuelAt_vanishing_actual_open_any O Wbase x ℓ).symm.trans (hProfilePhase ℓ)
    have hAtBase := hInitialHistory x.val (hOwindow x.val x.property) hProfileBase
    exact actual_native_original_function_open_restriction S aFull wFull Wbase
      (CartanIrreducible.cartanCoherence Wbase hWbase) Q₀ hDom.isWellFormed.isCoherent O x
        F₀ hF₀ id contMDiff_id hAtBase
  have hPoint (x : O) (hx : x ∈ Q.cosupp) :
      ActualHistoricalNativePointPresentation S aFull wFull Wphase Q x := by
    obtain ⟨Θ, hΘsrc, hΘ0, Γ, _d, hFive, hSpanAt, hCompAt, _hd, _hEq⟩ := hAnchored x hx
    exact ⟨Θ, hΘsrc, hΘ0, Γ, hFive, hSpanAt, hCompAt⟩
  have hState : HSTowerState (X := CMfd.of (n := n) O) Q Wphase (hilbertSamuelAt (vanishingIdeal (n := n) W) a₀) := by
    intro Y T hT
    exact hsTowerState_of_native (X := CMfd.of (n := n) O) W hW a₀ ha₀ Wphase hWphase Q hQN hQI S
      aFull wFull hWords hPositive hOwn hQMark hCutPhase hUpperPhase hPoint T hT
  have hz₀O : (z₀ : ComplexModel n) ∈ O' := ⟨z₀, hAllowedZero, rfl⟩
  refine ⟨U₁, V, η, O', hO'U, ⟨z₀.val, hz₀O⟩, Q, hMapZero, fun z => ?_, hDomPhase, hQN, hQE, ?_⟩
  · have hz : Opens.inclusion hO'U z ∈ O := z.property
    exact ((hmemO _).mp hz).2
  · have hWeq : Wphase = (Subtype.val : opensIn U₁ O' → U₁) ⁻¹' ((fun z : U₁ => (η z : M)) ⁻¹' W) := by
      change (Subtype.val : O → U₁) ⁻¹' Wbase = _
      rw [hSet]
    rw [← hWeq]
    intro Y T hT
    exact hState T hT

end

end Hironaka.HironakaG11PresNativePhase
