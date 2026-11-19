import Hironaka.Resolution.HironakaG1AdvancingSupportedBornContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1SupportedGapEmptyEpoch
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupRestrictOpen MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec ResolutionInvariantExt CanonicalCentres
  InvDomainTowerAlong InvDomainRebase RestrictEmptyTower
  HironakaG8GapNormalizedExponent ContactCanonicalAlong MarkedIdealOperationsAlong
  RelativePrincipalizationSpan GermIdealOrder TransformOffCentre BlowupControlledTransform
  TangentDirectionAlong HomogenizedIdealAlong CoefficientIdealRestriction ContactStageKept
  HironakaG8LocalHistory StepOneValue HironakaG1AdvancingSupportedBornContact

/-- Restriction to an open keeps the same ordinary-order gap. -/
theorem cosupport_gap_pullback_val {n : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : P.ideal.IsCoherent) (hGap : HasCosupportGap P) (U : Opens X) :
    HasCosupportGap (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) P) := by
  let P₁ := { P with d := 1 }
  have hHol : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hP h
  intro z hzN hz
  change z ∈ (MarkedIdeal.pullback (Subtype.val : U → X) P₁).cosupp at hz
  rw [cosupp_pullback_val P₁ hHol U] at hz
  rw [cosupp_pullback_val P hHol U]
  exact hGap z.val hzN hz

private theorem gap_empty_step {n : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : P.IsWellFormed) (hGap : HasCosupportGap P)
    (π : Y → X) (hπ : IsBlowupAlong n (∅ : Set X) π) :
    HasCosupportGap (P.geoTransform (∅ : Set X) π) := by
  let P₁ := {P with d := 1}
  have hHol : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hP.isCoherent h
  intro z _ hz
  have hPull := cosupport_subset_of_restrictLe (restrictLe_pullback_le_geoTransform
    (π := π) (∅ : Set X) P) 1 hz
  have hz₁ : z ∈ (P₁.geoTransform (∅ : Set X) π).cosupp :=
    cosupport_subset_of_restrictLe (restrictLe_geoTransform_empty_le_pullback hπ P₁) 1 hPull
  have hzBase : π z ∈ P₁.cosupp :=
    (mem_cosupp_geoTransform_iff P₁ hP.isClosedSubmanifold_N.1 hHol hπ (notMem_empty _)).mp hz₁
  exact (mem_cosupp_geoTransform_iff P hP.isClosedSubmanifold_N.1 hHol hπ (notMem_empty _)).mpr
    (hGap (π z) hzBase.1 hzBase)

set_option maxHeartbeats 1000000 in
/-- Controlled transforms through an empty epoch preserve the ordinary-order
gap. The actual controlled and total pullbacks agree on the carrier
for both marks in each empty step. -/
theorem cosupport_gap_geoTransformAlong_empty {n k : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) (hGap : HasCosupportGap P)
    (T : BlowupTower X Y) (hT : IsEmptyTower T) :
    HasCosupportGap (geoTransformAlong P T) := by
  induction T with
  | refl => exact hGap
  | step T Z π hπ ih =>
    obtain ⟨hOld, hZ⟩ := hT
    subst Z
    have hCur := isInvDomain_geoTransformAlong_of_isEmptyTower hP T hOld
    exact gap_empty_step (geoTransformAlong P T) hCur.isWellFormed (ih hOld) π hπ

set_option maxHeartbeats 1200000 in
/-- A genuine test preserves the gap over every source open missed by all
its centers. The result is for the literal controlled transform restricted
to the actual open preimage, with its inherited ordered boundary. -/
theorem cosupport_gap_geoTransformAlong_centresAvoid {n k : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) (hGap : HasCosupportGap P)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T) (U : Opens X)
    (hAvoid : CentresAvoid U T) :
    HasCosupportGap (X := CMfd.of (n := n) (openPreimage T U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong P T)) := by
  rw [← geoTransformAlong_restrict U hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent T hT]
  exact cosupport_gap_geoTransformAlong_empty _ (isInvDomain_pullback_val U hP)
    (cosupport_gap_pullback_val P hP.isWellFormed.isCoherent hGap U)
    (restrict U T) ((isEmptyTower_restrict_iff U T).mpr hAvoid)


open scoped Manifold ContDiff

private theorem cosupport_gap_pullback_diffeo {n : ℕ} {X Y : CMfd.{0} n}
    (e : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (P : MarkedIdeal n X) (hP : P.ideal.IsCoherent) (hGap : HasCosupportGap P) :
    HasCosupportGap (MarkedIdeal.pullback e P) := by
  let P₁ := {P with d := 1}
  intro z hzN hz
  change z ∈ (MarkedIdeal.pullback e P₁).cosupp at hz
  rw [MarkedIdealTowerTransport.cosupp_pullback_eq (Φ := e) (𝔪 := P₁) hP] at hz
  rw [MarkedIdealTowerTransport.cosupp_pullback_eq (Φ := e) (𝔪 := P) hP]
  exact hGap (e z) hzN hz

/-- In particular the supported gap holds on the actual selected mask if
that mask lies over a source open avoided by the tested head. -/
theorem cosupport_gap_on_stage_open_of_centresAvoid {n k : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) (hGap : HasCosupportGap P)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T)
    (U : Opens X) (hAvoid : CentresAvoid U T)
    (O : Opens Y) (hO : O ≤ openPreimage T U) :
    HasCosupportGap (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong P T)) := by
  let V := openPreimage T U
  let M := geoTransformAlong P T
  let A := CMfd.of (n := n) V
  let e := (MaxLocusLocal.nestedOpensDiffeo (n := n) hO).symm
  have hM := (isInvDomain_geoTransformAlong hP T hT).isWellFormed.isCoherent
  have hV := cosupport_gap_geoTransformAlong_centresAvoid P hP hGap T hT U hAvoid
  have hVc := GermIdealPullbackCalculus.isCoherent_pullback
    (f := (Subtype.val : A → Y)) contMDiff_subtype_val hM
  have hW := cosupport_gap_pullback_val (MarkedIdeal.pullback (M' := A) (Subtype.val : V → Y) M)
    hVc hV (MaxLocusLocal.nestedOpens V O)
  have hWc := GermIdealPullbackCalculus.isCoherent_pullback
    (f := (Subtype.val : MaxLocusLocal.nestedOpens V O → A)) contMDiff_subtype_val hVc
  have h := cosupport_gap_pullback_diffeo e _ hWc hW
  rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hM hO] at h


set_option maxHeartbeats 1100000 in
/-- The supported gap at the start of a tested epoch gives canonicality
transport on every actual stage mask lying over a center-free source
open. The head itself may have real centers elsewhere. -/
theorem advancing_supported_canonical_of_centresAvoid {n k l : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K P : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hP : IsInvDomain l P) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = P.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) P)
    (hGap : HasCosupportGap P)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H)
    (U : Opens X) (hAvoid : CentresAvoid U H) (O : Opens Y) (hO : O ≤ openPreimage H U) :
    let A := CMfd.of (n := n) O
    let D := contactMarkedKept K u H O
    let P' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong P H)
    ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
      IsCanonical D ((invFamily hn l).inv D) T ↔ IsCanonical P' ((invFamily hn l).inv P') T := by
  intro A D P' Z T
  have hHP := (advancing_kept_contact_supported_stage K P hK hP u hu hTrace hClass H hH O).1
  have hGap' := cosupport_gap_on_stage_open_of_centresAvoid P hP hGap H hHP U hAvoid O hO
  exact (advancing_kept_contact_supported_canonical hn K P hK hP u hu hTrace hClass H hH O hGap').2 T

end
end Hironaka.HironakaG1SupportedGapEmptyEpoch
