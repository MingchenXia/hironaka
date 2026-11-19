import Hironaka.Resolution.HironakaOriginalNCMarkedStratumBranchHistory
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumHistoryValue
import Hironaka.Resolution.HironakaOriginalNCBirthCanonicalContinuation
import Hironaka.Resolution.HironakaOriginalNCCausalAppendFrame
import Hironaka.Analytic.GrowingSeqTail
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Blowup.BlowupTowerIsoTail

/-!
# Whole native marked-stratum birth records on their actual empty windows

Only genuine open pullbacks, same native records, actual empty histories and
whole restricted equivalences are used. This is support for the subsequent
unconditional NEW-Psi canonical joint interpreter, with zero separate credit.
The numerical value is never replaced by the older coefficient/remainder Phi.
Mathematical route: joint-frame-design.md and its literal-restriction addendum.
Source-only initial implementation; no Lean/kernel acceptance is claimed.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumBirthFrame

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerSplitIso
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport MarkedIdealEquivalence.MarkedIdeal
  MaxLocusLocal BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdealOperationsAlong.MarkedIdeal GermIdealOrder GermIdealPullbackCalculus
  IdealWeightPowers MarkedIdealOperationsTransform BlowupExceptionalDivisor
  NormalCrossings HomogenizedGlueingTower MemberInterTowerAlong CoefficientIdealRestriction
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalOldBranchCountDrop
  HironakaOriginalNCCountHistory HironakaOriginalNCOldStratumStrictEquality
  HironakaOriginalNCMarkedStratum HironakaOriginalNCMarkedStratumHistoryValue
  HironakaOriginalNCMarkedStratumBranchHistory HironakaOriginalNCCausalHistoryValue
  HironakaOriginalNCBirthCanonicalContinuation HironakaOriginalNCCausalAppendFrame
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)

variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem count_congr {B : Type u} [TopologicalSpace B]
    [ChartedSpace (ComplexModel n) B] {H K : Set B}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hK : IsNormalCrossingsCarrier (n := n) K)
    (he : H = K) (b : B) : branchMultiplicity hH b = branchMultiplicity hK b := by
  subst K
  rfl

/-- All four fields of the NEW marked sum commute with the actual open inclusion. -/
theorem markedStratum_pullback_val (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    {A : Set X} (hA : IsClosedSubmanifold n A) (U : Opens X) :
    markedStratum (X := CMfd.of (n := n) U)
        (MarkedIdeal.pullback (Subtype.val : U → X) M) ((Subtype.val : U → X) ⁻¹' A) =
      MarkedIdeal.pullback (Subtype.val : U → X) (markedStratum M A) := by
  have hAU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hA U
  have hVA := VanishingIdealCoherent.isCoherent_vanishingIdeal hA
  have hVAU := VanishingIdealCoherent.isCoherent_vanishingIdeal hAU
  have hVan : GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) A) =
      vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' A) := by
    have hv := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) (V := U) (id : U → U) A
    rw [BlowupControlledTransform.pullback_id hVAU] at hv
    simpa only [Function.comp_id] using hv.symm
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := markedStratum (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) M) ((Subtype.val : U → X) ⁻¹' A))
    (𝔫 := MarkedIdeal.pullback (Subtype.val : U → X) (markedStratum M A)) rfl rfl ?_ rfl
  symm
  change GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (RestrictedIdealExtension.sumIdeal (idealPow M.ideal 1) (idealPow (vanishingIdeal (n := n) A) M.d)) = _
  rw [pullback_sumIdeal contMDiff_subtype_val
    (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
    (fun _ _ hg => holomorphicAt_of_mem_idealPow hg),
    pullback_idealPow contMDiff_subtype_val hI 1,
    pullback_idealPow contMDiff_subtype_val hVA M.d, hVan]
  rfl

/-- The genuine inverse map preserves the SAME whole marked sum, without a new ideal choice. -/
theorem markedStratum_pullback_diffeo {X' : CMfd.{u} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    {A : Set X} (hA : IsClosedSubmanifold n A) :
    markedStratum (MarkedIdeal.pullback φ M) (φ ⁻¹' A) =
      MarkedIdeal.pullback φ (markedStratum M A) := by
  have hAPre := MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
    φ.contMDiff φ.symm.contMDiff φ.apply_symm_apply φ.symm_apply_apply hA
  have hVA := VanishingIdealCoherent.isCoherent_vanishingIdeal hA
  have hVAPre := VanishingIdealCoherent.isCoherent_vanishingIdeal hAPre
  have hVan : GermIdeal.pullback (m := n) φ (vanishingIdeal (n := n) A) =
      vanishingIdeal (n := n) (φ ⁻¹' A) := by
    have hv := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
      φ.contMDiff φ.symm.contMDiff φ.apply_symm_apply φ.symm_apply_apply
      (g := id) contMDiff_id A
    rw [BlowupControlledTransform.pullback_id hVAPre] at hv
    simpa only [Function.comp_id] using hv.symm
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := markedStratum (X := X') (MarkedIdeal.pullback φ M) (φ ⁻¹' A))
    (𝔫 := MarkedIdeal.pullback φ (markedStratum M A)) rfl rfl ?_ rfl
  symm
  change GermIdeal.pullback (m := n) φ
      (RestrictedIdealExtension.sumIdeal (idealPow M.ideal 1) (idealPow (vanishingIdeal (n := n) A) M.d)) = _
  rw [pullback_sumIdeal φ.contMDiff
    (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
    (fun _ _ hg => holomorphicAt_of_mem_idealPow hg),
    pullback_idealPow φ.contMDiff hI 1, pullback_idealPow φ.contMDiff hVA M.d, hVan]
  rfl

private theorem strictAlong_empty (A : Set X) (hA : IsClosed A) :
    {Y : CMfd.{u} n} → (S : BlowupTower X Y) → IsEmptyTower S →
      strictAlong S A = S.proj ⁻¹' A
  | _, .refl, _he => rfl
  | _, .step S C π hπ, he => by
      obtain ⟨heS, rfl⟩ := he
      rw [strictAlong_step, strictAlong_empty A hA S heS]
      change closure (π ⁻¹' (S.proj ⁻¹' A \ ∅)) = (S.proj ∘ π) ⁻¹' A
      rw [sdiff_empty, ((hA.preimage S.contMDiff_proj.continuous).preimage
        hπ.contMDiff.continuous).closure_eq]
      rfl

/-- A true empty causal window identifies the ENTIRE new birth datum with
its current marked-stratum representative. The native N is not intersected
with the stratum, and no future canonical suffix is supplied or inferred. -/
theorem empty_birth_window (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y)
    (he : IsEmptyTower (causalBirthTail H T y)) :
    let k := T.length - birthYear H T y
    let D := tail T k
    let W := causalBirthOpen H T y
    let J := openPreimage D W
    let MJ := MarkedIdeal.pullback (Subtype.val : J → Y) (geoTransformAlong M T)
    let ZJ := {p : J | oldCount H T y ≤ oldCount H T p.val}
    IsInvDomain n (markedStratumBirth M H T y) ∧
      IsInvDomain n (markedStratum (X := CMfd.of (n := n) J) MJ ZJ) ∧
      RestrictEquiv (markedStratum (X := CMfd.of (n := n) J) MJ ZJ)
        (geoTransformAlong (markedStratumBirth M H T y) (causalBirthTail H T y)) ∧
      IsClosedSubmanifold n ZJ ∧ ∀ p : J, oldCount H T p.val ≤ oldCount H T y := by
  let k := T.length - birthYear H T y
  let K := head T k
  let D := tail T k
  let W := causalBirthOpen H T y
  let J := openPreimage D W
  let S := causalBirthTail H T y
  let MW := causalBirthParent M H T y
  let MJ := MarkedIdeal.pullback (Subtype.val : J → Y) (geoTransformAlong M T)
  let ZW := causalBirthStratum H T y
  let q := oldCount H T y
  let ZJ := {p : J | q ≤ oldCount H T p.val}
  have hK := ((isGeoTestTower_iff_head_tail M T k).mp hT).1
  have hD := ((isGeoTestTower_iff_head_tail M T k).mp hT).2
  have hHK := originalBranchHistory_head M T hHistory k
  have hcK := (current_old_strata_eq_strict M h K hK hHK).1
  have hcT := (current_old_strata_eq_strict M h T hT hHistory).1
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hMW : IsInvDomain n MW := InvDomainTowerAlong.isInvDomain_pullback_val W hKD
  have hTD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hMJ : IsInvDomain n MJ := InvDomainTowerAlong.isInvDomain_pullback_val J hTD
  let hW := boundaryAdapted_open W hcK
  let hJ := boundaryAdapted_open J hcT
  have hCount (p : W) : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) p =
      oldCount H K p.val :=
    (branchMultiplicity_open W (isNormalCrossingsCarrier_of_boundaryAdapted hcK)
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) p).trans
      (oldCount_eq K (isNormalCrossingsCarrier_of_boundaryAdapted hcK) p.val).symm
  have hBound : ∀ p : W,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) p ≤ q :=
    fun p => (hCount p).trans_le p.property
  have hZW : IsClosedSubmanifold n ZW := by
    have hEq : ZW = {p : W | q ≤ branchMultiplicity
        (isNormalCrossingsCarrier_of_boundaryAdapted hW) p} := by
      ext p
      change (q ≤ oldCount H K p.val) ↔ q ≤ branchMultiplicity
        (isNormalCrossingsCarrier_of_boundaryAdapted hW) p
      rw [hCount p]
    rw [hEq]
    exact isClosedSubmanifold_highest_superlevel
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) hBound
  have hOld : strictAlong S ((Subtype.val : W → (split T k).1) ⁻¹' strictAlong K H) =
      (Subtype.val : J → Y) ⁻¹' strictAlong T H := by
    change strictAlong (restrict W D) ((Subtype.val : W → (split T k).1) ⁻¹' strictAlong K H) = _
    rw [strictAlong_restrict W D (strictAlong K H)]
    have hc : strictAlong D (strictAlong K H) = strictAlong T H := by
      rw [← MemberInterLocusAlong.strictAlong_append, head_append_tail T k]
    rw [hc]
  have hNCS : IsNormalCrossingsCarrier (n := n)
      (strictAlong S ((Subtype.val : W → (split T k).1) ⁻¹' strictAlong K H)) :=
    hOld.symm ▸ isNormalCrossingsCarrier_of_boundaryAdapted hJ
  have hEmptyCount := branchMultiplicity_empty_tower
    (isNormalCrossingsCarrier_of_boundaryAdapted hW) S he hNCS
  have hCountJ (p : J) : oldCount H T p.val = oldCount H K (S.proj p).val := by
    calc
      oldCount H T p.val = branchMultiplicity
          (isNormalCrossingsCarrier_of_boundaryAdapted hcT) p.val := oldCount_eq T _ p.val
      _ = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hJ) p :=
        (branchMultiplicity_open J _ _ p).symm
      _ = branchMultiplicity hNCS p := (count_congr hNCS _ hOld p).symm
      _ = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) (S.proj p) := hEmptyCount p
      _ = oldCount H K (S.proj p).val := hCount (S.proj p)
  have hParent : geoTransformAlong MW S = MJ := by
    have hv := geoTransformAlong_restrict W hKD.isWellFormed.isClosedSubmanifold_N
      hKD.isWellFormed.isCoherent D hD
    have hc : geoTransformAlong (geoTransformAlong M K) D = geoTransformAlong M T := by
      rw [← geoTransformAlong_append, head_append_tail T k]
    simpa only [MW, causalBirthParent, S, causalBirthTail, D, K, k, hc] using hv
  have hCut : strictAlong S ZW = ZJ := by
    rw [strictAlong_empty ZW hZW.1 S he]
    ext p
    change (q ≤ oldCount H K (S.proj p).val) ↔ q ≤ oldCount H T p.val
    rw [hCountJ p]
  have hATest : IsGeoTestTower (markedStratumBirth M H T y) S :=
    isGeoTestTower_of_isEmptyTower _ S he
  have hA : IsInvDomain n (markedStratumBirth M H T y) :=
    (markedStratumBirth_domain M hM h T hT hHistory y).1
  have hAView : markedStratumBirth M H T y =
      markedStratum (X := CMfd.of (n := n) W) MW ZW := rfl
  have hTest : IsGeoTestTower (markedStratum (X := CMfd.of (n := n) W) MW ZW) S :=
    hAView ▸ hATest
  obtain ⟨hMTest, hHigh⟩ :=
    (markedStratum_test_tower_iff MW hMW.isWellFormed hMW.one_le_d hZW S).mp hTest
  have hStrict := (stratumFactor_tower_dictionary MW hMW.isWellFormed hZW S hMTest hHigh).2.1
  have hZJ : IsClosedSubmanifold n ZJ := hCut ▸ hStrict
  have hBJ : IsInvDomain n (markedStratum (X := CMfd.of (n := n) J) MJ ZJ) :=
    markedStratum_isInvDomain (X := CMfd.of (n := n) J) MJ hMJ hZJ
  have hRE := markedStratum_tower_restrictEquiv MW hMW.isWellFormed hMW.one_le_d hZW S hTest
  rw [hParent, hCut] at hRE
  refine ⟨hA, hBJ, ?_, hZJ, ?_⟩
  · simpa only [hAView] using InvDomainRebase.restrictEquiv_symm hRE
  · intro p
    exact (hCountJ p).trans_le (S.proj p).property

/-- The actual nested-open map transports the whole SAME marked-stratum record. -/
theorem markedStratum_nested_pullback (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (V J : Opens X) (hJV : J ≤ V) (A : Set X)
    (hAV : IsClosedSubmanifold n ((Subtype.val : V → X) ⁻¹' A)) :
    let O := nestedOpens V J
    let χ := (nestedOpensDiffeo (n := n) hJV).symm
    MarkedIdeal.pullback χ (MarkedIdeal.pullback (Subtype.val : O → V)
      (markedStratum (X := CMfd.of (n := n) V)
        (MarkedIdeal.pullback (Subtype.val : V → X) M) ((Subtype.val : V → X) ⁻¹' A))) =
      markedStratum (X := CMfd.of (n := n) J)
        (MarkedIdeal.pullback (Subtype.val : J → X) M) ((Subtype.val : J → X) ⁻¹' A) := by
  let O := nestedOpens V J
  let χ := (nestedOpensDiffeo (n := n) hJV).symm
  let MV := MarkedIdeal.pullback (Subtype.val : V → X) M
  let MO := MarkedIdeal.pullback (Subtype.val : O → V) MV
  let AV := (Subtype.val : V → X) ⁻¹' A
  let AO := (Subtype.val : O → V) ⁻¹' AV
  have hMVI : MV.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hI
  have hMOI : MO.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hMVI
  have hAO : IsClosedSubmanifold n AO :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hAV O
  have hParent : MarkedIdeal.pullback χ MO =
      MarkedIdeal.pullback (Subtype.val : J → X) M :=
    pullback_symm_nestedOpensDiffeo (M := X) hI hJV
  have hCut : χ ⁻¹' AO = (Subtype.val : J → X) ⁻¹' A := by
    ext x
    rfl
  have hOpen := markedStratum_pullback_val (X := CMfd.of (n := n) V) MV hMVI hAV O
  have hDiff := markedStratum_pullback_diffeo
    (X := CMfd.of (n := n) O) (X' := CMfd.of (n := n) J) χ MO hMOI hAO
  dsimp only
  rw [← hOpen, ← hDiff, hParent, hCut]

/-- Native canonicality of ONE actual common prefix supplies its SAME
canonical future on every genuine nested subopen, with all actual years. -/
theorem canonical_markedStratum_nested (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (V J : Opens X) (hJV : J ≤ V) (A : Set X)
    (hAV : IsClosedSubmanifold n ((Subtype.val : V → X) ⁻¹' A))
    {D : CMfd.{u} n} (Q : BlowupTower (CMfd.of (n := n) V) D)
    (hCan : IsCanonical
      (markedStratum (X := CMfd.of (n := n) V)
        (MarkedIdeal.pullback (Subtype.val : V → X) M) ((Subtype.val : V → X) ⁻¹' A))
      ((CanonicalCentres.canonicalInvariant n).inv
        (markedStratum (X := CMfd.of (n := n) V)
          (MarkedIdeal.pullback (Subtype.val : V → X) M) ((Subtype.val : V → X) ⁻¹' A))) Q) :
    let O := nestedOpens V J
    let χ := (nestedOpensDiffeo (n := n) hJV).symm
    let B := markedStratum (X := CMfd.of (n := n) J)
      (MarkedIdeal.pullback (Subtype.val : J → X) M) ((Subtype.val : J → X) ⁻¹' A)
    let F := transport χ (restrict O Q)
    IsInvDomain n B ∧ IsCanonical B ((CanonicalCentres.canonicalInvariant n).inv B) F.tower ∧
      F.tower.length = Q.length := by
  let O := nestedOpens V J
  let χ := (nestedOpensDiffeo (n := n) hJV).symm
  let AV := markedStratum (X := CMfd.of (n := n) V)
    (MarkedIdeal.pullback (Subtype.val : V → X) M) ((Subtype.val : V → X) ⁻¹' A)
  let B := markedStratum (X := CMfd.of (n := n) J)
    (MarkedIdeal.pullback (Subtype.val : J → X) M) ((Subtype.val : J → X) ⁻¹' A)
  let F := transport χ (restrict O Q)
  let R := CanonicalCentres.canonicalInvariant n
  have hMV := InvDomainTowerAlong.isInvDomain_pullback_val V hM
  have hAVDom : IsInvDomain n AV := markedStratum_isInvDomain _ hMV hAV
  have hAO := InvDomainTowerAlong.isInvDomain_pullback_val O hAVDom
  have hB := markedStratum_nested_pullback M hM.isWellFormed.isCoherent V J hJV A hAV
  have hBDom : IsInvDomain n B := by
    have hd := InvDomainTowerAlong.isInvDomain_pullback χ hAO
    rw [hB] at hd
    exact hd
  have hCanO := Seq.ResolutionInvariantExt.isCanonical_restrict R hAVDom O Q hCan
  have hIso := transport_isTowerIso χ (restrict O Q)
  have hCanJ : IsCanonical B (R.inv B) F.tower := by
    have hc := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hAO χ hIso hCanO
    rw [hB] at hc
    exact hc
  exact ⟨hBDom, hCanJ, by rw [length_transport, length_restrict]⟩

/-- The SAME current native parent on its exact intrinsic low open, with the
ambient count equations added at mark one. No future tower is chosen. -/
def phaseAuxiliary (M : MarkedIdeal n X) (H : Set X) (K : BlowupTower X Y) (q : ℕ) :
    MarkedIdeal n (oldCountLowOpen H K q) :=
  markedStratum (X := CMfd.of (n := n) (oldCountLowOpen H K q))
    (MarkedIdeal.pullback (Subtype.val : oldCountLowOpen H K q → Y) (geoTransformAlong M K))
    {p | q ≤ oldCount H K p.val}

/-- The genuine low-open highest geometry produces the current phase domain
for EVERY q; neither its native intersection nor any future is a premise. -/
theorem phaseAuxiliary_domain (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : BlowupTower X Y) (hK : IsGeoTestTower M K)
    (hHistory : IsOriginalBranchTestTower M H K) (q : ℕ) :
    IsInvDomain n (phaseAuxiliary M H K q) ∧
      IsClosedSubmanifold n {p : oldCountLowOpen H K q | q ≤ oldCount H K p.val} := by
  let V := oldCountLowOpen H K q
  let hc := (current_old_strata_eq_strict M h K hK hHistory).1
  let hV := boundaryAdapted_open V hc
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hMV := InvDomainTowerAlong.isInvDomain_pullback_val V hCurrent
  have hCount (p : V) : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) p =
      oldCount H K p.val :=
    (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hV) p).trans (oldCount_eq K _ p.val).symm
  have hBound : ∀ p : V,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) p ≤ q :=
    fun p => (hCount p).trans_le p.property
  have hCut : {p : V | q ≤ oldCount H K p.val} =
      {p : V | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) p} := by
    ext p
    change (q ≤ oldCount H K p.val) ↔ q ≤ branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted hV) p
    rw [hCount p]
  have hZ : IsClosedSubmanifold n {p : V | q ≤ oldCount H K p.val} := by
    rw [hCut]
    exact isClosedSubmanifold_highest_superlevel
      (isNormalCrossingsCarrier_of_boundaryAdapted hV) hBound
  exact ⟨markedStratum_isInvDomain (X := CMfd.of (n := n) V) _ hMV hZ, hZ⟩

/-- ONE internally canonical common phase continues every SAME empty birth
at its top count. The returned future is the genuine nested restriction of
that SAME Q, and the complete lower record/value comparison is an output. -/
theorem same_empty_birth_phase_continuation (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : BlowupTower X Y) (hK : IsGeoTestTower M K)
    (hHistory : IsOriginalBranchTestTower M H K)
    (hEmpty : HasEmptyCausalBirthTails M H K) (q : ℕ)
    {D : CMfd.{u} n} (Q : BlowupTower (CMfd.of (n := n) (oldCountLowOpen H K q)) D)
    (hCan : IsCanonical (phaseAuxiliary M H K q)
      ((CanonicalCentres.canonicalInvariant n).inv (phaseAuxiliary M H K q)) Q)
    (x : Y) (hx : x ∈ (geoTransformAlong M K).cosupp) (hxq : oldCount H K x = q) :
    let k := K.length - birthYear H K x
    let W := causalBirthOpen H K x
    let S := causalBirthTail H K x
    let J := openPreimage (tail K k) W
    let A := markedStratumBirth M H K x
    let B := markedStratum (X := CMfd.of (n := n) J)
      (MarkedIdeal.pullback (Subtype.val : J → Y) (geoTransformAlong M K))
      {p | q ≤ oldCount H K p.val}
    ∃ hJV : J ≤ oldCountLowOpen H K q,
      let O := nestedOpens (oldCountLowOpen H K q) J
      let χ := (nestedOpensDiffeo (n := n) hJV).symm
      let F := transport χ (restrict O Q)
      IsInvDomain n A ∧ IsInvDomain n B ∧
        RestrictEquiv B (geoTransformAlong A S) ∧
        IsCanonical B ((CanonicalCentres.canonicalInvariant n).inv B) F.tower ∧
        IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) (S.append F.tower) ∧
        (geoTransformAlong A (S.append F.tower)).E = (geoTransformAlong B F.tower).E ∧
        (geoTransformAlong A (S.append F.tower)).cosupp = (geoTransformAlong B F.tower).cosupp ∧
        ∀ z ∈ (geoTransformAlong B F.tower).cosupp,
          (CanonicalCentres.canonicalInvariant n).inv A (S.append F.tower) z =
            (CanonicalCentres.canonicalInvariant n).inv B F.tower z := by
  let k := K.length - birthYear H K x
  let W := causalBirthOpen H K x
  let S := causalBirthTail H K x
  let J := openPreimage (tail K k) W
  let V := oldCountLowOpen H K q
  let A := markedStratumBirth M H K x
  let B := markedStratum (X := CMfd.of (n := n) J)
    (MarkedIdeal.pullback (Subtype.val : J → Y) (geoTransformAlong M K))
    {p | q ≤ oldCount H K p.val}
  have he : IsEmptyTower S := hEmpty x hx
  obtain ⟨hA, hB, hRE, _hZJ, hBound⟩ := empty_birth_window M hM h K hK hHistory x he
  have hB' : IsInvDomain n B := by simpa only [hxq] using hB
  have hRE' : RestrictEquiv B (geoTransformAlong A S) := by simpa only [hxq] using hRE
  have hJV : J ≤ V := by
    intro p hp
    exact (hBound ⟨p, hp⟩).trans_eq hxq
  refine ⟨hJV, ?_⟩
  let O := nestedOpens V J
  let χ := (nestedOpensDiffeo (n := n) hJV).symm
  let F := transport χ (restrict O Q)
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hZV := (phaseAuxiliary_domain M hM h K hK hHistory q).2
  have hNested := canonical_markedStratum_nested (geoTransformAlong M K) hKD V J hJV
    {p : Y | q ≤ oldCount H K p} hZV Q hCan
  obtain ⟨_hBNested, hCanB, _hLen⟩ := hNested
  have hFuture := empty_history_canonical_continuation (CanonicalCentres.canonicalInvariant n)
    A hA S he B hB'.isWellFormed.isCoherent hRE'
  obtain ⟨_hAS, _hBDomain, hFutures⟩ := hFuture
  obtain ⟨_hIff, hActual⟩ := hFutures F.tower
  obtain ⟨hCanA, _hBTest, _hATest, hE, hCosupp, _hMax, _hLength, hValues⟩ := hActual hCanB
  exact ⟨hA, hB', hRE', hCanB, hCanA, hE, hCosupp, hValues⟩

/-! Exact NEW-value append data and generic native nested-tower transport. -/

private def evaluateFrame (M : MarkedIdeal n X) (H : Set X) {Z : CMfd.{u} n}
    (y : Z) (q : ℕ)
    (frame : Σ B : CMfd.{u} n, BlowupTower X B × BlowupTower B Z) :
    ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
  let K := frame.2.1
  let D := frame.2.2
  let W := oldCountLowOpen H K q
  let MW := MarkedIdealBiholomorphism.MarkedIdeal.pullback
    (Subtype.val : W → frame.1) (geoTransformAlong M K)
  let A := markedStratum (X := CMfd.of (n := n) W) MW
    {z : W | q ≤ oldCount H K z.val}
  let S := restrict W D
  if hp : y ∈ openPreimage D W then
    let p : openPreimage D W := ⟨y, hp⟩
    toLex (q, if p ∈ (geoTransformAlong A S).cosupp then
      ((CanonicalCentres.canonicalInvariant n).inv A S p : WithBot (CanonicalCentres.ValTy n)) else ⊥)
  else toLex (q, ⊥)

private theorem markedStratumHistoryValue_eq_evaluateFrame
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (y : Y) :
    markedStratumHistoryValue M H T y =
      evaluateFrame M H y (oldCount H T y) (split T (T.length - birthYear H T y)) := by
  have hp : y ∈ openPreimage (split T (T.length - birthYear H T y)).2.2
      (oldCountLowOpen H (split T (T.length - birthYear H T y)).2.1 (oldCount H T y)) :=
    (causalBirthPoint H T y).property
  unfold evaluateFrame
  dsimp only
  rw [dif_pos hp]
  rfl

/-- This is the DEFINED NEW marked-stratum Psi at the current append, expressed on
the SAME new marked-stratum birth datum and its literal continued restricted suffix.
The no-count-drop condition is a pointwise geometric case, not a future
canonicality or value certificate. The natural highest phase derives it
internally at each surviving highest-count point by actual antitonicity. -/
theorem markedStratumHistoryValue_append_of_count_eq (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) (P : BlowupTower Y Z) (y : Z)
    (he : oldCount H (T.append P) y = oldCount H T (P.proj y)) :
    let x := P.proj y
    let k := T.length - birthYear H T x
    let D := tail T k
    let W := causalBirthOpen H T x
    let A := markedStratumBirth M H T x
    let S := restrict W (D.append P)
    let p : openPreimage (D.append P) W :=
      ⟨y, by
        change (D.append P).proj y ∈ W
        rw [BlowupTower.proj_append]
        exact (causalBirthPoint H T (P.proj y)).property⟩
    markedStratumHistoryValue M H (T.append P) y =
      toLex (oldCount H T x,
        if p ∈ (geoTransformAlong A S).cosupp then
          ((CanonicalCentres.canonicalInvariant n).inv A S p : WithBot (CanonicalCentres.ValTy n))
        else ⊥) := by
  have hβ := birthYear_append_of_count_eq H T P y he
  have hIndex : (T.append P).length - birthYear H (T.append P) y =
      (T.length - birthYear H T (P.proj y)) + P.length := by
    rw [BlowupTower.length_append, hβ]
    have hb := birthYear_le_length H T (P.proj y)
    omega
  let k := T.length - birthYear H T (P.proj y)
  let frame : Σ B : CMfd.{u} n, BlowupTower X B × BlowupTower B Z :=
    ⟨(split T k).1, head T k, (tail T k).append P⟩
  have hFrame : split (T.append P) ((T.append P).length - birthYear H (T.append P) y) = frame := by
    rw [hIndex, split_append_removed_tail T k P]
  have hAux : evaluateFrame M H y (oldCount H (T.append P) y)
      (split (T.append P) ((T.append P).length - birthYear H (T.append P) y)) =
      evaluateFrame M H y (oldCount H T (P.proj y)) frame := by
    rw [he, hFrame]
  dsimp only
  rw [markedStratumHistoryValue_eq_evaluateFrame]
  refine hAux.trans ?_
  have hp : y ∈ openPreimage frame.2.2
      (oldCountLowOpen H frame.2.1 (oldCount H T (P.proj y))) := by
    change ((tail T k).append P).proj y ∈ causalBirthOpen H T (P.proj y)
    rw [BlowupTower.proj_append]
    exact (causalBirthPoint H T (P.proj y)).property
  unfold evaluateFrame
  dsimp only
  rw [dif_pos hp]
  rfl

private theorem pullback_id_coherent (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    MarkedIdeal.pullback (id : X → X) M = M :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
    (show M.E.map (fun C => (id : X → X) ⁻¹' C) = M.E by simp)
    (BlowupControlledTransform.pullback_id hI) rfl

private theorem nested_prefix_of_actual_ambient_extension
    (V J : Opens X) (hJV : J ≤ V)
    {D : CMfd.{u} n} (Q : BlowupTower (CMfd.of (n := n) V) D)
    (P : BlowupTower X Y)
    (e : D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ openPreimage P V)
    (hIso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) V ∞) Q (restrict V P) e) :
    let O := nestedOpens V J
    let χ := (nestedOpensDiffeo (n := n) hJV).symm
    let F := transport χ (restrict O Q)
    ∃ ξ : F.target ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ openPreimage P J,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) J ∞) F.tower (restrict J P) ξ ∧
        ∀ z : F.target, (ξ z).val = (e (F.back z : openPreimage Q O).val).val := by
  let O := nestedOpens V J
  let χ := (nestedOpensDiffeo (n := n) hJV).symm
  let F := transport χ (restrict O Q)
  have hMatch : ∀ v : V, v ∈ O ↔
      Diffeomorph.refl 𝓘(ℂ, ComplexModel n) V ∞ v ∈ O := fun _ => Iff.rfl
  have hLast := StepOneTangentChange.isTowerIso_mem_openPreimage_iff hIso hMatch
  let eO := StepOneTangentChange.diffeoOpens e (openPreimage Q O) (openPreimage (restrict V P) O) hLast
  let eJ := nestedDiffeo (n := n) (openPreimage P V) (openPreimage (restrict V P) O)
    (openPreimage P J) (mem_openPreimage_restrict_nestedOpens V J P) (openPreimage_mono P hJV)
  let ξ := F.back.trans (eO.trans eJ)
  have hRestricted := StepOneTangentChange.isTowerIso_restrictOpens hMatch hIso hLast
  have hNested := isTowerIso_restrict_nestedOpens hJV P
  have hTransport := transport_isTowerIso χ (restrict O Q)
  have hComposed := hTransport.trans (hRestricted.trans hNested)
  refine ⟨ξ, BlowupTowerSplitIso.IsTowerIso.congr_base hComposed (fun z => ?_), fun _ => rfl⟩
  apply Subtype.ext
  rfl
private theorem selected_prefix_subopen_value
    (V J : Opens X) (hJV : J ≤ V)
    (A : MarkedIdeal n (CMfd.of (n := n) V)) (hA : IsInvDomain n A)
    {D : CMfd.{u} n} (Q : BlowupTower (CMfd.of (n := n) V) D)
    (hCan : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) Q) (j : ℕ) :
    let O := nestedOpens V J
    let χ := (nestedOpensDiffeo (n := n) hJV).symm
    let AO := MarkedIdeal.pullback (Subtype.val : O → V) A
    let B := MarkedIdeal.pullback χ AO
    let Qj := head Q j
    let F := transport χ (restrict O Qj)
    ∀ p : F.target,
      (p ∈ (geoTransformAlong B F.tower).cosupp ↔
        (F.back p).val ∈ (geoTransformAlong A Qj).cosupp) ∧
      ((F.back p).val ∈ (geoTransformAlong A Qj).cosupp →
        (CanonicalCentres.canonicalInvariant n).inv B F.tower p =
          (CanonicalCentres.canonicalInvariant n).inv A Qj (F.back p).val) := by
  let R := CanonicalCentres.canonicalInvariant n
  let O := nestedOpens V J
  let χ := (nestedOpensDiffeo (n := n) hJV).symm
  let AO := MarkedIdeal.pullback (Subtype.val : O → V) A
  let B := MarkedIdeal.pullback χ AO
  let Qj := head Q j
  let F := transport χ (restrict O Qj)
  have hQj := isCanonical_head A (R.inv A) Q j hCan
  have hAO := InvDomainTowerAlong.isInvDomain_pullback_val O hA
  have hCanO := Seq.ResolutionInvariantExt.isCanonical_restrict R hA O Qj hQj
  have hTestQj := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue hA Qj hQj
  have hTestO := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    R.isInvValue hAO (restrict O Qj) hCanO
  have hIso := transport_isTowerIso χ (restrict O Qj)
  have hCosOpen := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hA.isWellFormed.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent O Qj hTestQj
  have hCos := IsTowerIso.cosupp_geoTransformAlong χ hAO.isWellFormed.isClosedSubmanifold_N
    hAO.isWellFormed.isCoherent hIso hTestO
  rw [hCosOpen] at hCos
  dsimp only
  intro p
  refine ⟨?_, ?_⟩
  · change p ∈ (geoTransformAlong (MarkedIdeal.pullback χ AO) F.tower).cosupp ↔ _
    rw [hCos]
    rfl
  · intro hp
    have hpO : F.back p ∈ (geoTransformAlong AO (restrict O Qj)).cosupp := by
      rw [hCosOpen]
      exact hp
    have hInvTower := R.isInvValue.towerIso χ AO hAO F.tower (restrict O Qj) F.back hIso hCanO p hpO
    have hInvOpen := R.isInvValue.restrictOpen A hA O Qj hQj (F.back p) hp
    exact hInvTower.trans hInvOpen

private theorem causal_value_on_internal_birth_continuation
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y)
    (P : BlowupTower Y Z) (y : Z)
    (he : oldCount H (T.append P) y = oldCount H T (P.proj y)) :
    let W := causalBirthOpen H T (P.proj y)
    let D := tail T (T.length - birthYear H T (P.proj y))
    let J := openPreimage D W
    let A := markedStratumBirth M H T (P.proj y)
    let S := causalBirthTail H T (P.proj y)
    let p : openPreimage P J := ⟨y, (causalBirthPoint H T (P.proj y)).property⟩
    ∀ {B : CMfd.{u} n} (F : BlowupTower (CMfd.of (n := n) J) B)
      (ξ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ openPreimage P J),
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) J ∞) F (restrict J P) ξ →
      IsInvDomain n A →
      IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) (S.append F) →
      markedStratumHistoryValue M H (T.append P) y =
        toLex (oldCount H T (P.proj y),
          if ξ.symm p ∈ (geoTransformAlong A (S.append F)).cosupp then
            ((CanonicalCentres.canonicalInvariant n).inv A (S.append F) (ξ.symm p) :
              WithBot (CanonicalCentres.ValTy n))
          else ⊥) := by
  let W := causalBirthOpen H T (P.proj y)
  let D := tail T (T.length - birthYear H T (P.proj y))
  let J := openPreimage D W
  let A := markedStratumBirth M H T (P.proj y)
  let S := causalBirthTail H T (P.proj y)
  let R := CanonicalCentres.canonicalInvariant n
  let pJ : openPreimage P J := ⟨y, (causalBirthPoint H T (P.proj y)).property⟩
  dsimp only
  intro B F ξ hIso hA hCan
  let L := restrict W (D.append P)
  let pL : openPreimage (D.append P) W :=
    ⟨y, by
      change (D.append P).proj y ∈ W
      rw [BlowupTower.proj_append]
      exact pJ.property⟩
  let α := opensCongr (n := n) (openPreimage_append D P W).symm
  let η := α.trans ξ.symm
  have hAppendIso := isTowerIso_restrict_append W D P
  have hCanonicalFutureIso := (IsTowerIso.refl_self S).append hIso
  have hTotal0 := hAppendIso.trans hCanonicalFutureIso.symm
  have hTotal : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) W ∞) L (S.append F) η :=
    BlowupTowerSplitIso.IsTowerIso.congr_base hTotal0 (fun _ => rfl)
  have hPoint : η pL = ξ.symm pJ := by
    apply congrArg (fun v => ξ.symm v)
    apply Subtype.ext
    rfl
  have hId := pullback_id_coherent (X := CMfd.of (n := n) W) A hA.isWellFormed.isCoherent
  have hTest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    R.isInvValue hA (S.append F) hCan
  have hCos := IsTowerIso.cosupp_geoTransformAlong
    (X := CMfd.of (n := n) W) (X' := CMfd.of (n := n) W) (𝔪 := A)
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) W ∞)
    hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent hTotal hTest
  change (geoTransformAlong (MarkedIdeal.pullback (id : W → W) A) L).cosupp = _ at hCos
  rw [hId] at hCos
  have hMask : pL ∈ (geoTransformAlong A L).cosupp ↔
      ξ.symm pJ ∈ (geoTransformAlong A (S.append F)).cosupp := by
    rw [hCos]
    change η pL ∈ (geoTransformAlong A (S.append F)).cosupp ↔ _
    rw [hPoint]
  have hOriginal := markedStratumHistoryValue_append_of_count_eq M H T P y he
  change markedStratumHistoryValue M H (T.append P) y =
    toLex (oldCount H T (P.proj y),
      if pL ∈ (geoTransformAlong A L).cosupp then
        (R.inv A L pL : WithBot (CanonicalCentres.ValTy n)) else ⊥) at hOriginal
  rw [hOriginal]
  by_cases hp : pL ∈ (geoTransformAlong A L).cosupp
  · have hTarget := hMask.mp hp
    rw [if_pos hp, if_pos hTarget]
    have hInv := R.isInvValue.towerIso
      (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) W ∞) A hA L (S.append F) η hTotal hCan pL
      (by rw [hPoint]; exact hTarget)
    change R.inv (MarkedIdeal.pullback (id : W → W) A) L pL = R.inv A (S.append F) (η pL) at hInv
    rw [hId, hPoint] at hInv
    exact congrArg (fun v : CanonicalCentres.ValTy n =>
      toLex (oldCount H T (P.proj y), (v : WithBot (CanonicalCentres.ValTy n)))) hInv
  · have hTarget : ξ.symm pJ ∉ (geoTransformAlong A (S.append F)).cosupp :=
      fun ht => hp (hMask.mpr ht)
    rw [if_neg hp, if_neg hTarget]

private def canonicalBirthFrame (M : MarkedIdeal n X) (H : Set X)
    {Y : CMfd.{u} n} (q : ℕ)
    (frame : Σ B : CMfd.{u} n, BlowupTower X B × BlowupTower B Y) : Prop :=
  let K := frame.2.1
  let D := frame.2.2
  let W := oldCountLowOpen H K q
  let MW := MarkedIdeal.pullback (Subtype.val : W → frame.1) (geoTransformAlong M K)
  let A := markedStratum (X := CMfd.of (n := n) W) MW {z : W | q ≤ oldCount H K z.val}
  IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) (restrict W D)

private theorem birth_canonical_append_of_count_eq
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (P : BlowupTower Y Z) (y : Z)
    (he : oldCount H (T.append P) y = oldCount H T (P.proj y))
    (hCan : IsCanonical (markedStratumBirth M H T (P.proj y))
      ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H T (P.proj y)))
      (restrict (causalBirthOpen H T (P.proj y))
        ((tail T (T.length - birthYear H T (P.proj y))).append P))) :
    IsCanonical (markedStratumBirth M H (T.append P) y)
      ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H (T.append P) y))
      (causalBirthTail H (T.append P) y) := by
  have hβ := birthYear_append_of_count_eq H T P y he
  have hIndex : (T.append P).length - birthYear H (T.append P) y =
      (T.length - birthYear H T (P.proj y)) + P.length := by
    rw [BlowupTower.length_append, hβ]
    have hb := birthYear_le_length H T (P.proj y)
    omega
  have hFrame : split (T.append P) ((T.append P).length - birthYear H (T.append P) y) =
      ⟨(split T (T.length - birthYear H T (P.proj y))).1,
        head T (T.length - birthYear H T (P.proj y)),
        (tail T (T.length - birthYear H T (P.proj y))).append P⟩ := by
    rw [hIndex, split_append_removed_tail T (T.length - birthYear H T (P.proj y)) P]
  change canonicalBirthFrame M H (oldCount H (T.append P) y)
    (split (T.append P) ((T.append P).length - birthYear H (T.append P) y))
  rw [he, hFrame]
  exact hCan


private theorem canonical_birth_tail_of_actual_future
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (P : BlowupTower Y Z) (y : Z)
    (he : oldCount H (T.append P) y = oldCount H T (P.proj y)) :
    let W := causalBirthOpen H T (P.proj y)
    let D := tail T (T.length - birthYear H T (P.proj y))
    let J := openPreimage D W
    let A := markedStratumBirth M H T (P.proj y)
    let S := causalBirthTail H T (P.proj y)
    ∀ {B : CMfd.{u} n} (F : BlowupTower (CMfd.of (n := n) J) B)
      (ξ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ openPreimage P J),
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) J ∞) F (restrict J P) ξ →
      IsInvDomain n A → IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) (S.append F) →
      IsCanonical (markedStratumBirth M H (T.append P) y)
        ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H (T.append P) y))
        (causalBirthTail H (T.append P) y) := by
  let W := causalBirthOpen H T (P.proj y)
  let D := tail T (T.length - birthYear H T (P.proj y))
  let J := openPreimage D W
  let A := markedStratumBirth M H T (P.proj y)
  let S := causalBirthTail H T (P.proj y)
  let R := CanonicalCentres.canonicalInvariant n
  dsimp only
  intro B F ξ hIso hA hCan
  let L := restrict W (D.append P)
  let α := opensCongr (n := n) (openPreimage_append D P W).symm
  let η := α.trans ξ.symm
  have hAppendIso := isTowerIso_restrict_append W D P
  have hFutureIso := (IsTowerIso.refl_self S).append hIso
  have hTotal0 := hAppendIso.trans hFutureIso.symm
  have hTotal : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) W ∞) L (S.append F) η :=
    BlowupTowerSplitIso.IsTowerIso.congr_base hTotal0 (fun _ => rfl)
  have hCanLocal := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (X := CMfd.of (n := n) W)
    (X' := CMfd.of (n := n) W) (𝔪 := A) R hA
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) W ∞) hTotal hCan
  change IsCanonical (MarkedIdeal.pullback (id : W → W) A)
    (R.inv (MarkedIdeal.pullback (id : W → W) A)) L at hCanLocal
  rw [pullback_id_coherent (X := CMfd.of (n := n) W) A hA.isWellFormed.isCoherent] at hCanLocal
  exact birth_canonical_append_of_count_eq M H T P y he hCanLocal



/-- The DEFINED new value and SAME literal birth tail at an arbitrary
surviving top-count point are read on the actual common restricted phase.
Every no-drop, native domain and lower future canonicality is produced. -/
theorem phase_value_at_top (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : BlowupTower X Y) (hK : IsGeoTestTower M K)
    (hHistoryK : IsOriginalBranchTestTower M H K) (hEmpty : HasEmptyCausalBirthTails M H K)
    (q : ℕ) (hCover : (geoTransformAlong M K).cosupp ⊆ oldCountLowOpen H K q)
    (P : BlowupTower Y Z) (hP : IsGeoTestTower (geoTransformAlong M K) P)
    (hHistoryP : IsOriginalBranchTestTower (geoTransformAlong M K) (strictAlong K H) P)
    (hCan : IsCanonical (phaseAuxiliary M H K q)
      ((CanonicalCentres.canonicalInvariant n).inv (phaseAuxiliary M H K q))
      (restrict (oldCountLowOpen H K q) P))
    (p : openPreimage P (oldCountLowOpen H K q))
    (hy : p.val ∈ (geoTransformAlong M (K.append P)).cosupp)
    (hTop : oldCount H (K.append P) p.val = q) :
    IsCanonical (markedStratumBirth M H (K.append P) p.val)
        ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H (K.append P) p.val))
        (causalBirthTail H (K.append P) p.val) ∧
      markedStratumHistoryValue M H (K.append P) p.val =
        toLex (q, if p ∈ (geoTransformAlong (phaseAuxiliary M H K q)
            (restrict (oldCountLowOpen H K q) P)).cosupp then
          ((CanonicalCentres.canonicalInvariant n).inv (phaseAuxiliary M H K q)
            (restrict (oldCountLowOpen H K q) P) p : WithBot (CanonicalCentres.ValTy n)) else ⊥) := by
  let V := oldCountLowOpen H K q
  let MC := geoTransformAlong M K
  let A := phaseAuxiliary M H K q
  let Q := restrict V P
  let R := CanonicalCentres.canonicalInvariant n
  let x := P.proj p.val
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hAD := (phaseAuxiliary_domain M hM h K hK hHistoryK q).1
  have hZV := (phaseAuxiliary_domain M hM h K hK hHistoryK q).2
  have hy' : p.val ∈ (geoTransformAlong MC P).cosupp := by
    simpa only [MC, geoTransformAlong_append] using hy
  have hx : x ∈ MC.cosupp := TransformOffCentre.cosupp_geoTransformAlong_subset MC
    hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent P hP hy'
  have hUpper : oldCount H K x ≤ q := hCover hx
  have hLower := oldCount_append_le_native M hM.isWellFormed h K hK hHistoryK P hP hHistoryP p.val
  have he : oldCount H (K.append P) p.val = oldCount H K x := by
    change oldCount H (K.append P) p.val ≤ oldCount H K x at hLower
    omega
  have hxq : oldCount H K x = q := he.symm.trans hTop
  obtain ⟨hJV, hBirthA, hB, hRE, hCanB, hBirthCan, _hBirthE, hBirthCos, hBirthValues⟩ :=
    same_empty_birth_phase_continuation M hM h K hK hHistoryK hEmpty q Q hCan x hx hxq
  let W := causalBirthOpen H K x
  let Dold := tail K (K.length - birthYear H K x)
  let J := openPreimage Dold W
  let BirthA := markedStratumBirth M H K x
  let BirthS := causalBirthTail H K x
  let O := nestedOpens V J
  let χ := (nestedOpensDiffeo (n := n) hJV).symm
  let F := transport χ (restrict O Q)
  let B := markedStratum (X := CMfd.of (n := n) J)
    (MarkedIdeal.pullback (Subtype.val : J → Y) MC) {z | q ≤ oldCount H K z.val}
  obtain ⟨ξ, hFIso, hUnderlying⟩ := nested_prefix_of_actual_ambient_extension V J hJV Q P
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (openPreimage P V) ∞) (IsTowerIso.refl_self Q)
  let pJ : openPreimage P J := ⟨p.val, (causalBirthPoint H K x).property⟩
  let z := ξ.symm pJ
  have hPoint : (F.back z).val = p := by
    apply Subtype.ext
    have hu := hUnderlying z
    change (ξ z).val = (F.back z).val.val at hu
    rw [Diffeomorph.apply_symm_apply] at hu
    exact hu.symm
  have hRecord : MarkedIdeal.pullback χ (MarkedIdeal.pullback (Subtype.val : O → V) A) = B :=
    markedStratum_nested_pullback MC hKD.isWellFormed.isCoherent V J hJV
      {z : Y | q ≤ oldCount H K z} hZV
  have hFreshAll {E : CMfd.{u} n}
      (Q' : BlowupTower (CMfd.of (n := n) V) E)
      (hQ' : IsCanonical A (R.inv A) Q') :
      let F' := transport χ (restrict O Q')
      ∀ w : F'.target,
        (w ∈ (geoTransformAlong (MarkedIdeal.pullback χ
              (MarkedIdeal.pullback (Subtype.val : O → V) A)) F'.tower).cosupp ↔
          (F'.back w).val ∈ (geoTransformAlong A Q').cosupp) ∧
        ((F'.back w).val ∈ (geoTransformAlong A Q').cosupp →
          R.inv (MarkedIdeal.pullback χ
              (MarkedIdeal.pullback (Subtype.val : O → V) A)) F'.tower w =
            R.inv A Q' (F'.back w).val) := by
    cases Q' with
    | refl =>
        exact selected_prefix_subopen_value V J hJV A hAD .refl hQ' 0
    | step Q' C π hπ =>
        exact selected_prefix_subopen_value V J hJV A hAD (.step Q' C π hπ) hQ' 0
  have hFresh := hFreshAll Q hCan z
  rw [hRecord] at hFresh
  obtain ⟨hFreshMask, hFreshValues⟩ := hFresh
  rw [hPoint] at hFreshMask hFreshValues
  have hValue := causal_value_on_internal_birth_continuation M H K P p.val he
    F.tower ξ hFIso hBirthA hBirthCan
  have hCanBirth := canonical_birth_tail_of_actual_future M H K P p.val he
    F.tower ξ hFIso hBirthA hBirthCan
  refine ⟨hCanBirth, ?_⟩
  change markedStratumHistoryValue M H (K.append P) p.val =
    toLex (oldCount H K x, if z ∈ (geoTransformAlong BirthA (BirthS.append F.tower)).cosupp then
      (R.inv BirthA (BirthS.append F.tower) z : WithBot (CanonicalCentres.ValTy n)) else ⊥) at hValue
  rw [hxq, hBirthCos] at hValue
  change markedStratumHistoryValue M H (K.append P) p.val =
    toLex (q, if p ∈ (geoTransformAlong A Q).cosupp then
      (R.inv A Q p : WithBot (CanonicalCentres.ValTy n)) else ⊥)
  by_cases hp : p ∈ (geoTransformAlong A Q).cosupp
  · have hzB := hFreshMask.mpr hp
    rw [if_pos hzB, hBirthValues z hzB, hFreshValues hp] at hValue
    simpa only [if_pos hp] using hValue
  · have hzB : z ∉ (geoTransformAlong B F.tower).cosupp := fun hz => hp (hFreshMask.mp hz)
    rw [if_neg hzB] at hValue
    simpa only [if_neg hp] using hValue

/-- BOTH directions identify the whole auxiliary cosupport with ENTIRE
native count-q cosupport, on the literal actual common restriction. -/
theorem phase_whole_cosupp (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : BlowupTower X Y) (hK : IsGeoTestTower M K)
    (hHistoryK : IsOriginalBranchTestTower M H K) (q : ℕ)
    (P : BlowupTower Y Z) (hP : IsGeoTestTower (geoTransformAlong M K) P)
    (hHistoryP : IsOriginalBranchTestTower (geoTransformAlong M K) (strictAlong K H) P)
    (hATest : IsGeoTestTower (phaseAuxiliary M H K q) (restrict (oldCountLowOpen H K q) P)) :
    (geoTransformAlong (phaseAuxiliary M H K q) (restrict (oldCountLowOpen H K q) P)).cosupp =
      {p : openPreimage P (oldCountLowOpen H K q) |
        p.val ∈ (geoTransformAlong M (K.append P)).cosupp ∧ oldCount H (K.append P) p.val = q} := by
  let V := oldCountLowOpen H K q
  let MC := geoTransformAlong M K
  let MV := MarkedIdeal.pullback (Subtype.val : V → Y) MC
  let Q := restrict V P
  let hcK := (current_old_strata_eq_strict M h K hK hHistoryK).1
  let hv := boundaryAdapted_open V hcK
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hMV := InvDomainTowerAlong.isInvDomain_pullback_val V hKD
  have hCount (p : V) : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hv) p =
      oldCount H K p.val :=
    (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hcK)
      (isNormalCrossingsCarrier_of_boundaryAdapted hv) p).trans (oldCount_eq K _ p.val).symm
  have hBound : ∀ p : V,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hv) p ≤ q :=
    fun p => (hCount p).trans_le p.property
  have hZeq : {p : V | q ≤ oldCount H K p.val} =
      {p : V | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hv) p} := by
    ext p
    change (q ≤ oldCount H K p.val) ↔ q ≤ branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted hv) p
    rw [hCount p]
  have hTest : IsGeoTestTower (markedStratum (X := CMfd.of (n := n) V) MV
      {p : V | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hv) p}) Q := by
    have ht : IsGeoTestTower (markedStratum (X := CMfd.of (n := n) V) MV
        {p : V | q ≤ oldCount H K p.val}) (restrict V P) := hATest
    rw [hZeq] at ht
    exact ht
  have hLocal := markedStratum_test_history (X := CMfd.of (n := n) V) MV hMV.isWellFormed
    hMV.one_le_d hv q hBound Q hTest
  have hCos : (geoTransformAlong (phaseAuxiliary M H K q) Q).cosupp =
      {p | p ∈ (geoTransformAlong MV Q).cosupp ∧
        oldCount ((Subtype.val : V → Y) ⁻¹' strictAlong K H) Q p = q} := by
    change (geoTransformAlong (markedStratum (X := CMfd.of (n := n) V) MV
      {p : V | q ≤ oldCount H K p.val}) Q).cosupp = _
    rw [hZeq]
    exact hLocal.2.2
  have hCurrent := geoTransformAlong_restrict V hKD.isWellFormed.isClosedSubmanifold_N
    hKD.isWellFormed.isCoherent P hP
  have hMP := InvDomainTowerAlong.isInvDomain_geoTransformAlong hKD P hP
  have hCosParent := cosupp_pullback_val (geoTransformAlong MC P)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hMP.isWellFormed.isCoherent hg) (openPreimage P V)
  rw [hCurrent, hCosParent] at hCos
  have hCountCurrent (p : openPreimage P V) :
      oldCount ((Subtype.val : V → Y) ⁻¹' strictAlong K H) Q p =
        oldCount H (K.append P) p.val :=
    (oldCount_restrict_native MC hKD.isWellFormed hcK P hP hHistoryP V p).trans
      (oldCount_append_data H K P p.val).symm
  rw [hCos]
  ext p
  change (p.val ∈ (geoTransformAlong MC P).cosupp ∧
    oldCount ((Subtype.val : V → Y) ⁻¹' strictAlong K H) Q p = q) ↔ _
  rw [hCountCurrent p]
  rw [geoTransformAlong_append]
  rfl

/-- Actual lower testness supplies native parent tests and ALL old branches
on the common low open, before any global future test is known. -/
theorem phase_local_test_history (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : BlowupTower X Y) (hK : IsGeoTestTower M K)
    (hHistoryK : IsOriginalBranchTestTower M H K) (q : ℕ)
    (P : BlowupTower Y Z)
    (hATest : IsGeoTestTower (phaseAuxiliary M H K q) (restrict (oldCountLowOpen H K q) P)) :
    let V := oldCountLowOpen H K q
    let MV := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong M K)
    IsGeoTestTower MV (restrict V P) ∧
      IsOriginalBranchTestTower MV ((Subtype.val : V → Y) ⁻¹' strictAlong K H) (restrict V P) := by
  let V := oldCountLowOpen H K q
  let MC := geoTransformAlong M K
  let MV := MarkedIdeal.pullback (Subtype.val : V → Y) MC
  let hcK := (current_old_strata_eq_strict M h K hK hHistoryK).1
  let hv := boundaryAdapted_open V hcK
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hMV := InvDomainTowerAlong.isInvDomain_pullback_val V hKD
  have hCount (p : V) : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hv) p =
      oldCount H K p.val :=
    (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hcK)
      (isNormalCrossingsCarrier_of_boundaryAdapted hv) p).trans (oldCount_eq K _ p.val).symm
  have hBound : ∀ p : V,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hv) p ≤ q :=
    fun p => (hCount p).trans_le p.property
  have hZeq : {p : V | q ≤ oldCount H K p.val} =
      {p : V | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hv) p} := by
    ext p
    change (q ≤ oldCount H K p.val) ↔ q ≤ branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted hv) p
    rw [hCount p]
  have hTest : IsGeoTestTower (markedStratum (X := CMfd.of (n := n) V) MV
      {p : V | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hv) p}) (restrict V P) := by
    have ht : IsGeoTestTower (markedStratum (X := CMfd.of (n := n) V) MV
        {p : V | q ≤ oldCount H K p.val}) (restrict V P) := hATest
    rw [hZeq] at ht
    exact ht
  have hh := markedStratum_test_history (X := CMfd.of (n := n) V) MV hMV.isWellFormed
    hMV.one_le_d hv q hBound (restrict V P) hTest
  exact ⟨hh.1, hh.2.1⟩

/-- Empty birth windows retain membership in their SAME actual transformed
auxiliary cosupport, via the entire marked-stratum representative identity. -/
theorem empty_birth_membership (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y)
    (hy : y ∈ (geoTransformAlong M T).cosupp) (he : IsEmptyTower (causalBirthTail H T y)) :
    causalBirthPoint H T y ∈
      (geoTransformAlong (markedStratumBirth M H T y) (causalBirthTail H T y)).cosupp := by
  let k := T.length - birthYear H T y
  let W := causalBirthOpen H T y
  let J := openPreimage (tail T k) W
  let MJ := MarkedIdeal.pullback (Subtype.val : J → Y) (geoTransformAlong M T)
  let ZJ := {p : J | oldCount H T y ≤ oldCount H T p.val}
  let p := causalBirthPoint H T y
  obtain ⟨_hA, _hB, hRE, hZJ, _hBound⟩ := empty_birth_window M hM h T hT hHistory y he
  have hTD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hMJ := InvDomainTowerAlong.isInvDomain_pullback_val J hTD
  have hpM : p ∈ MJ.cosupp := by
    rw [cosupp_pullback_val (geoTransformAlong M T)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hTD.isWellFormed.isCoherent hg) J]
    exact hy
  have hpB : p ∈ (markedStratum (X := CMfd.of (n := n) J) MJ ZJ).cosupp := by
    rw [markedStratum_cosupp (X := CMfd.of (n := n) J) MJ
      hMJ.isWellFormed hMJ.one_le_d (Z := ZJ) hZJ]
    refine ⟨hpM, ?_⟩
    change oldCount H T y ≤ oldCount H T y
    exact le_rfl
  rw [← hRE.cosupp_eq]
  exact hpB

end
end Hironaka.HironakaOriginalNCMarkedStratumBirthFrame
