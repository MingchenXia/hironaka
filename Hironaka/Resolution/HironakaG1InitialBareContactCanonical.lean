import Hironaka.Resolution.HironakaG1ProperNormalZeroPhase
import Hironaka.Resolution.HironakaG1PrescribedContactBarRecoding
import Hironaka.Invariant.StepOneEmptyPrefix

/-! Canonicality of the bare coefficient cut on an initial zero-phase suffix. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1InitialBareContactCanonical

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  RelativePrincipalizationSpan GermIdealOrder DivisorExponentAlong
  HomogenizedIdealAlong StepOneValue StepOneRegime StepOneValueMasked
  StepOneEmptyPrefix
  ContactStageKept TangentDirectionAlong CoefficientIdealRestriction
  HironakaG8LocalHistory HironakaG8GapNormalizedExponent HironakaG11InvBMClass
  HironakaActualCoefficientDivisorExponentGap HironakaCoherentTransformExtension
  HironakaG1ProperNormalZeroPhase HironakaG1PrescribedContactBarRecoding
  HironakaG1CoefficientCarrierClassData HironakaG1OriginalUnequalMarkCanonical
  InvDomainTowerAlong

private theorem gap_pullback_open {n : ℕ} {X : CMfd.{0} n}
    (C : MarkedIdeal n X) (hC : C.ideal.IsCoherent) (hGap : HasCosupportGap C) (O : Opens X) :
    HasCosupportGap (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → X) C) := by
  let C₁ := { C with d := 1 }
  have hHol : ∀ x f, C.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hC h
  intro z hzN hz
  change z ∈ (MarkedIdeal.pullback (Subtype.val : O → X) C₁).cosupp at hz
  rw [cosupp_pullback_val C₁ hHol O] at hz
  rw [cosupp_pullback_val C hHol O]
  exact hGap z.val hzN hz

private theorem coefficient_contact_gap {n k : ℕ} {X : CMfd.{0} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain k K) {F : Set X} (hF : F ⊆ K.N) :
    HasCosupportGap (withN (coeffMarkedAlong K) F) := by
  intro z _ hz
  have hEq := coefficient_restriction_cosupport_gap K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d F hF
  change z ∈ cosupport n F (coeffMarkedAlong K).ideal (coeffMarkedAlong K).d
  rw [← hEq]
  exact hz

set_option maxHeartbeats 1200000 in
/-- When the actual zero run begins at the source, the original Step One
canonical suffix is canonical on its literal bare coefficient contact.
The contact retains its own mark and the actual restricted tower. -/
theorem initial_zero_stepOne_bare_contact_canonical {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain (k + 1) K)
    (hMax : IsMaximalOrderAlong K.N K.ideal K.d) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (T : BlowupTower X Y)
    (hCan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) K) T)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp)
    (hl : level K T y = 0) (hNS : ¬ IsSpecial K T y)
    (hRun : regimeRun (stepRegime K 0) T y = T.length) :
    let F := K.N ∩ {z | u z = 0}
    let C := withN (coeffMarkedAlong K) F
    let O := maskB K (.refl : BlowupTower X X) (T.proj y)
    let C' := MarkedIdeal.pullback (Subtype.val : O → X) C
    IsInvDomain k C → ∃ hp : T.proj y ∈ O,
      IsCanonical C' ((invFamily hn k).inv C') (restrict O T) ∧
      (⟨y, hp⟩ : openPreimage T O) ∈ (geoTransformAlong C' (restrict O T)).cosupp := by
  intro F C O C' hC
  let R := invFamily hn k
  let D := withN (coeffMarkedAlong (barMarked K)) F
  let D' := MarkedIdeal.pullback (Subtype.val : O → X) D
  let Data {A : CMfd.{0} n} (H : BlowupTower X A) (S : BlowupTower A Y) : Prop :=
    let W := maskB K H (S.proj y)
    let P := contactMarkedKept K u H W
    ∃ hp : S.proj y ∈ W,
      IsCanonical P (R.inv P) (restrict W S) ∧
        (⟨y, hp⟩ : openPreimage S W) ∈ (geoTransformAlong P (restrict W S)).cosupp
  let r := regimeRun (stepRegime K 0) T y
  have hData : Data (head T r) (tail T r) := by
    obtain ⟨hp, _, _, _, _, _, _, _, _, _, hCanD, hzD, _⟩ :=
      prescribed_contact_zero_phase hn K hK hMax u hu T hCan y hy hl hNS
    exact ⟨hp, hCanD, hzD⟩
  change Data (head T (regimeRun (stepRegime K 0) T y))
    (tail T (regimeRun (stepRegime K 0) T y)) at hData
  rw [hRun] at hData
  change Data (split T T.length).2.1 (split T T.length).2.2 at hData
  rw [split_of_length_le T T.length le_rfl] at hData
  obtain ⟨hp, hDCan, hDz⟩ : ∃ hp : T.proj y ∈ O,
      IsCanonical D' (R.inv D') (restrict O T) ∧
      (⟨y, hp⟩ : openPreimage T O) ∈ (geoTransformAlong D' (restrict O T)).cosupp := hData
  obtain ⟨hD, hClass, _⟩ := prescribed_contact_bar_data hn K hK u hu hC
  have hC' : IsInvDomain k C' := isInvDomain_pullback_val O hC
  have hD' : IsInvDomain k D' := isInvDomain_pullback_val O hD
  have hLocal : LocWPEquiv (X := CMfd.of (n := n) O) C' D' := hClass.restrict O
  have hKBar := isInvDomain_barMarked (X := X) K hK
  have hF : F ⊆ K.N := inter_subset_left
  have hGapC := gap_pullback_open C hC.isWellFormed.isCoherent (coefficient_contact_gap K hK hF) O
  have hGapD := gap_pullback_open D hD.isWellFormed.isCoherent
    (coefficient_contact_gap (barMarked K) hKBar hF) O
  have hCarrier : C'.N = D'.N := rfl
  have hDim := SameCarrierDim.of_N_eq (X := CMfd.of (n := n) O) hCarrier
  have hExp := normalized_exponents_of_gap_sameCarrierDim hn (X := CMfd.of (n := n) O)
    C' D' hC' hD' hLocal hDim hGapC hGapD
  have hCCan := (invFamily_isCanonical_iff_of_local hn (X := CMfd.of (n := n) O)
    C' D' hC' hD' hLocal hDim hExp (restrict O T)).mpr hDCan
  have hCT := R.isInvValue.isGeoTestTower_of_isCanonical hC' (restrict O T) hCCan
  exact ⟨hp, hCCan, ((hLocal.wEquiv.2 _).2 hCT).symm ▸ hDz⟩

end

end Hironaka.HironakaG1InitialBareContactCanonical
