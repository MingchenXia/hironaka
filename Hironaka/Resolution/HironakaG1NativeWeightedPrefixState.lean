import Hironaka.Resolution.HironakaG11PresLineStable
import Hironaka.Resolution.HironakaG1WeightedChartTransport
import Hironaka.Resolution.HironakaG1SourceWeakClassGraphLift

/-! The intrinsic native state and actual weighted point presentations
along a common source test prefix. -/
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NativeWeightedPrefixState

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaG8LocalHistory HironakaG8LocalHistory.LHist HironakaG8MixedEquiv
  HironakaG11PresLineState HironakaG11PresLineStable HironakaActualProjectionTestRecord
  HironakaG1WeightedChartTransport HironakaActualFixedInheritedSelector
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis HironakaActualWeightedCoefficientCompression
  HironakaSmoothSubmersionGermIdealColon HironakaActualHistoricalNativeStageStep
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentTranslatedJets
  HironakaSmoothCentreCoherentDomain RelativePrincipalizationSpan
  HironakaG1SourceWeakClassGraphLift HironakaG1NormalSelectorGraph MarkedIdealBiholomorphism

open scoped ProductComplexManifold

variable {n : ℕ} {X : CMfd.{0} n} {E : List (Set X)}

/-- The intrinsic source subset at an actual prefix, using strict
transform for a blowup and inverse image for a line or open restriction. -/
def nativeSetAlong (W : Set X) :
    {m : ℕ} → {Y : CMfd.{0} m} → {F : List (Set Y)} → LHist X E Y F → Set Y
  | _, _, _, .refl => W
  | m, _, _, .controlled T _ π _ => strictTransform m π (nativeSetAlong W T)
  | _, _, _, .projection T => Prod.fst ⁻¹' nativeSetAlong W T
  | m, _, _, .exceptional T _ _ _ π _ => strictTransform m π (nativeSetAlong W T)
  | _, _, _, .restrict T U => (Subtype.val : U → _) ⁻¹' nativeSetAlong W T

/-- The Hilbert–Samuel value is retained through blowups and open
restrictions and convolves with a line at each projection test. -/
def nativeValueAlong (H : ℕ → ℕ) :
    {m : ℕ} → {Y : CMfd.{0} m} → {F : List (Set Y)} → LHist X E Y F → ℕ → ℕ
  | _, _, _, .refl => H
  | _, _, _, .controlled T _ _ _ => nativeValueAlong H T
  | _, _, _, .projection T => lineHS (nativeValueAlong H T)
  | _, _, _, .exceptional T _ _ _ _ _ => nativeValueAlong H T
  | _, _, _, .restrict T _ => nativeValueAlong H T

/-- The native point presentations at a later test prefix are produced
from the original record by the actual source transforms. -/
theorem nativeHSState_at_test_prefix {P : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ}
    (hP : NativeHSState P W H) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (T : LHist X P.E Y F),
      InKinds Kinds.wp T → IsTest P T →
      NativeHSState (record P T) (nativeSetAlong W T) (nativeValueAlong H T)
  | _, _, _, .refl, _, _ => hP
  | _, _, _, .controlled T C π hπ, hk, ht =>
    (nativeHSState_at_test_prefix hP T hk ht.1).geoTransform ht.2.1 ht.2.2.1 hπ
  | _, _, _, .projection T, hk, ht =>
    nativeLineStability (record P T) (nativeSetAlong W T) (nativeValueAlong H T)
      (nativeHSState_at_test_prefix hP T hk.2 ht)
  | _, _, _, .exceptional _ _ _ _ _ _, hk, _ => by
    have hfalse : false = true := hk.1
    contradiction
  | _, _, _, .restrict T U, hk, ht =>
    (nativeHSState_at_test_prefix hP T hk ht).restrict U

/-- The original independent native records give native states for the
same actual intrinsic subset and HS value at every common test prefix. -/
theorem independent_nativeHSStates_at_test_prefix {P Q : MarkedIdeal n X}
    {W : Set X} {H : ℕ → ℕ} (hP : NativeHSState P W H) (hQ : NativeHSState Q W H)
    (hE : Q.E = P.E) {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)}
    (T : LHist X P.E Y F) (hk : InKinds Kinds.wp T) (ht : IsTest P T) :
    NativeHSState (record P T) (nativeSetAlong W T) (nativeValueAlong H T) ∧
    NativeHSState (record (withBoundary Q P.E) T) (nativeSetAlong W T) (nativeValueAlong H T) := by
  have hQ' : NativeHSState (withBoundary Q P.E) W H := by rwa [withBoundary_eq hE]
  have htQ := ((locWPEquiv_native hP hQ hE).isTest_iff T hk).mp ht
  exact ⟨nativeHSState_at_test_prefix hP T hk ht, nativeHSState_at_test_prefix hQ' T hk htQ⟩

/-- The actual invariant-domain record persists along the same source
test prefix, including every line product and open restriction. -/
theorem isInvDomain_at_native_test_prefix {P : MarkedIdeal n X} {k : ℕ}
    (hP : IsInvDomain k P) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (T : LHist X P.E Y F),
      InKinds Kinds.wp T → IsTest P T → ∃ l : ℕ, IsInvDomain l (record P T)
  | _, _, _, .refl, _, _ => ⟨k, hP⟩
  | _, _, _, .controlled T C π hπ, hk, ht => by
    obtain ⟨l, hStage⟩ := isInvDomain_at_native_test_prefix hP T hk ht.1
    have hOne : IsGeoTestTower (record P T) (.step .refl C π hπ) := ⟨trivial, ht.2⟩
    exact ⟨l, InvDomainTowerAlong.isInvDomain_geoTransformAlong hStage (.step .refl C π hπ) hOne⟩
  | _, _, _, .projection T, hk, ht => by
    obtain ⟨l, hStage⟩ := isInvDomain_at_native_test_prefix hP T hk.2 ht
    exact ⟨l + 1, projection_test_isInvDomain _ hStage⟩
  | _, _, _, .exceptional _ _ _ _ _ _, hk, _ => by
    have hfalse : false = true := hk.1
    contradiction
  | _, _, _, .restrict T U, hk, ht => by
    obtain ⟨l, hStage⟩ := isInvDomain_at_native_test_prefix hP T hk ht
    exact ⟨l, InvDomainTowerAlong.isInvDomain_pullback_val U hStage⟩


/-- A native weighted extraction retains its original selector, diagram,
mark and actual chart, and realizes its entire ideals in the chosen
comparison chart. -/
def NativePointExtractionInChart {m : ℕ} {Y : CMfd.{0} m}
    (R : MarkedIdeal m Y) (W : Set Y) (y : Y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel m) y y))
    (hΘ : Θ.toFun (chartAt (ComplexModel m) y y) = 0) : Prop :=
  ∃ (V : Finset (Fin m →₀ ℕ)) (S : ActualFixedInheritedSelector V) (s : ℕ)
    (a : Fin s ≃ V) (words : Fin s → CoordinateWord m)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel m) y y))
    (_hΦsrc : Φ.source ⊆ (chartAt (ComplexModel m) y).target)
    (hΦ : Φ.toFun (chartAt (ComplexModel m) y y) = 0)
    (Γ : V → HolGerm (ComplexModel m)),
    let Γ' := adaptedChartGermEquiv y Φ Θ hΦ hΘ ∘ Γ
    (∀ i, wordExponent (words i) = (a i).val) ∧
    (∀ v : V, 0 < normalExponentDegree v.val) ∧
    R.d = weightedCommonMark (fun v : V => normalExponentDegree v.val) ∧
    ActualHistoricalFivePointLaws S a words Γ ∧
    Ideal.span (range (fun i => Γ (a i))) = originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n := m) W) y Φ) 0) ∧
    Ideal.span (range Γ') = adaptedIdeal (vanishingIdeal (n := m) W) y Θ hΘ ∧
    adaptedIdeal R.ideal y Θ hΘ =
      weightedCompression (fun v : V => normalExponentDegree v.val) Γ'

/-- The native state itself produces the actual weighted point extraction
in a supplied comparison chart through the actual holomorphic transition. -/
theorem native_point_extraction_of_state {m : ℕ} {Y : CMfd.{0} m}
    {R : MarkedIdeal m Y} {W : Set Y} {H : ℕ → ℕ} (hR : NativeHSState R W H)
    {y : Y} (hy : y ∈ R.cosupp)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel m) y y))
    (hΘ : Θ.toFun (chartAt (ComplexModel m) y y) = 0) :
    NativePointExtractionInChart R W y Θ hΘ := by
  obtain ⟨_, hW, _, _, V, S, s, a, words, hWords, hPos, _, hMark, _, _, hAt⟩ := hR
  have hWI := CartanIrreducible.cartanCoherence W hW
  obtain ⟨Φ, hΦsrc, hΦ, Γ, hFive, hSpan, hOrigin, hComp⟩ :=
    native_point_weighted_data_in_given_chart S a words W hWI R y (hAt y hy) Θ hΘ
  exact ⟨V, S, s, a, words, Φ, hΦsrc, hΦ, Γ, hWords, hPos, hMark, hFive, hSpan, hOrigin, hComp⟩

/-- Both independent weighted extractions at a later prefix present the
same original analytic ideal in the comparison chart. Their weighted
compressions and marks retain their own native data. -/
theorem independent_native_extractions_at_test_prefix {P Q : MarkedIdeal n X}
    {W : Set X} {H : ℕ → ℕ} (hP : NativeHSState P W H) (hQ : NativeHSState Q W H)
    (hE : Q.E = P.E) {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)}
    (T : LHist X P.E Y F) (hk : InKinds Kinds.wp T) (ht : IsTest P T)
    {y : Y} (hy : y ∈ (record P T).cosupp)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel m) y y))
    (hΘ : Θ.toFun (chartAt (ComplexModel m) y y) = 0) :
    NativePointExtractionInChart (record P T) (nativeSetAlong W T) y Θ hΘ ∧
    NativePointExtractionInChart (record (withBoundary Q P.E) T) (nativeSetAlong W T) y Θ hΘ := by
  obtain ⟨hP', hQ'⟩ := independent_nativeHSStates_at_test_prefix hP hQ hE T hk ht
  have hCos : (record P T).cosupp = (record (withBoundary Q P.E) T).cosupp :=
    hP'.cosupp_eq.trans hQ'.cosupp_eq.symm
  exact ⟨native_point_extraction_of_state hP' hy Θ hΘ, native_point_extraction_of_state hQ' (hCos ▸ hy) Θ hΘ⟩

/-- A later coordinate-open stage inherits the graph-supported test
comparison from its original native inputs. Its two source domains and
native states are produced by the common prefix. -/
theorem locWPEquiv_selectorMarked_after_native_test_prefix
    {k l : ℕ} (P Q : MarkedIdeal n X) (hPdom : IsInvDomain k P) (hQdom : IsInvDomain l Q)
    {W : Set X} {H : ℕ → ℕ} (hP : NativeHSState P W H) (hQ : NativeHSState Q W H)
    (hE : Q.E = P.E) {m : ℕ} {U : Opens (ComplexModel m)} {F : List (Set U)}
    (T : LHist X P.E (CMfd.of (n := m) U) F) (hk : InKinds Kinds.wp T) (ht : IsTest P T)
    {f g : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (G : List (Set (HironakaActualOpenZeroSectionDifferentials.productOpen U))) :
    let R := record P T
    let S := record (withBoundary Q P.E) T
    let Y := CMfd.of (n := m + 1) (HironakaActualOpenZeroSectionDifferentials.productOpen U)
    LocWPEquiv (X := Y) (selectorMarked f R (G.map (graphShift f g ⁻¹' ·)))
      (MarkedIdeal.pullback (M := Y) (M' := Y) (graphShift f g) (selectorMarked g S G)) := by
  obtain ⟨hP', hQ'⟩ := independent_nativeHSStates_at_test_prefix hP hQ hE T hk ht
  obtain ⟨_, hPD⟩ := isInvDomain_at_native_test_prefix hPdom T hk ht
  have hQdom' : IsInvDomain l (withBoundary Q P.E) := by rwa [withBoundary_eq hE]
  have htQ := ((locWPEquiv_native hP hQ hE).isTest_iff T hk).mp ht
  obtain ⟨_, hQD⟩ := isInvDomain_at_native_test_prefix hQdom' T hk htQ
  exact locWPEquiv_selectorMarked_of_native (record P T) (record (withBoundary Q P.E) T)
    hPD hQD hP' hQ' rfl hf hg G

end

end Hironaka.HironakaG1NativeWeightedPrefixState
