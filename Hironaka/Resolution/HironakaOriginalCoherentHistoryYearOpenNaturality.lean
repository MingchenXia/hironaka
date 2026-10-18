/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCoherentCompanionCountIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.Invariant.MonomialPartEtale
/-! Actual whole carrier/derivative/Nm and original history-year ideals commute
with true original open histories, retaining every actual empty step. Whole
current-boundary auxiliary marked records agree. Complete source-first math
precedes code; full arbitrary recursive analytic closure/scheduler remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCoherentHistoryYearOpenNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  GermIdealOrder NonmonomialOrderLocal MonomialPartAlong RestrictedIdealExtension
  DerivativeIdealAlong DerivativeIdealAlongCoherent DerivativeIdealAlongEtale
  HironakaOriginalCoherentHistoryYearIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

private theorem hol_of_coherent {I : GermIdeal n X} (h : I.IsCoherent) :
    ∀ x g,I.mem x g → HolomorphicAt n g x :=
  fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h hg

/-- Whole real relative carrier-order equations commute with the genuine open inclusion. -/
theorem pullback_val_carrierOrderIdeal {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) (U : Opens X) (q : ℕ) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (carrierOrderIdeal N I q) =
      carrierOrderIdeal (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) q := by
  cases q with
  | zero => exact SmoothCentreHomogeneity.pullback_val_vanishingIdeal U N
  | succ q =>
    rw [carrierOrderIdeal,MarkedIdealOperationsTransform.pullback_sumIdeal contMDiff_subtype_val
      (hol_of_coherent (VanishingIdealCoherent.isCoherent_vanishingIdeal hN))
      (hol_of_coherent (isCoherent_iterDerivIdealAlong hI hN q)),
      SmoothCentreHomogeneity.pullback_val_vanishingIdeal U N,
      pullback_val_iterDerivIdealAlong U (hol_of_coherent hI) q]
    rfl

private theorem actual_nm_coherent (hn : 0 < n) {m : MarkedIdeal n X} (h : IsInvDomain k m) :
    (nmPart m).IsCoherent :=
  isCoherent_nonmonomialPartAlong hn h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isSNCDivisor h.isWellFormed.isTransverse h.isWellFormed.isCoherent h.isNonzeroAlongAt

/-- The SAME actual Nm part and whole relative order ideal commute with actual original open pullback. -/
theorem pullback_val_nonmonomialOrderIdeal (hn : 0 < n) {m : MarkedIdeal n X}
    (h : IsInvDomain k m) (U : Opens X) (q : ℕ) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (nonmonomialOrderIdeal m q) =
      nonmonomialOrderIdeal (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) m) q := by
  have hM := isCoherent_monomialPartAlong hn h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isSNCDivisor h.isWellFormed.isTransverse h.isWellFormed.isCoherent h.isNonzeroAlongAt
  have hNN := actual_nm_coherent hn h
  have hEq := MonomialPartEtale.pullback_nonmonomialPartAlong
    (fun y : U => ⟨openInv U y,isLocalInverseAt_val U y⟩) h.isWellFormed.isCoherent hM hNN
  rw [nonmonomialOrderIdeal,pullback_val_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N hNN U q]
  change carrierOrderIdeal (X := CMfd.of (n := n) U) _
    (GermIdeal.pullback (m := n) (Subtype.val : U → X) (nmPart m)) q = _
  rw [hEq]
  rfl

/-- Both actual baseline factors pull back as their SAME original open marked record. -/
theorem pullback_val_companionYearBaselineIdeal (hn : 0 < n) {m : MarkedIdeal n X}
    (h : IsInvDomain k m) (U : Opens X) (q : ℕ) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (companionYearBaselineIdeal m q) =
      companionYearBaselineIdeal (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) m) q := by
  rw [companionYearBaselineIdeal,MarkedIdealOperationsTransform.pullback_sumIdeal
    (𝔞 := carrierOrderIdeal m.N m.ideal m.d) (𝔟 := nonmonomialOrderIdeal m q) contMDiff_subtype_val
    (hol_of_coherent (isCoherent_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent m.d))
    (hol_of_coherent (isCoherent_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N (actual_nm_coherent hn h) q)),
    pullback_val_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent U m.d,
    pullback_val_nonmonomialOrderIdeal hn h U q]
  rfl

private def actualRestrictedBlowupOpen {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (V : Opens Y) : Opens Z :=
  ⟨π ⁻¹' (V : Set Y),V.isOpen.preimage hπ.contMDiff.continuous⟩

/-- The genuine original blowup's actual open lift, with true preimage membership. -/
def actualRestrictedBlowupMap {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (V : Opens Y) : actualRestrictedBlowupOpen hπ V → V :=
  fun z => ⟨π z,z.property⟩

private theorem actualRestrictedBlowupMap_holomorphic {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (V : Opens Y) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualRestrictedBlowupMap hπ V) :=
  (ContMDiff.subtypeVal_comp_iff _ _).mp (hπ.contMDiff.comp contMDiff_subtype_val)

/-- The two SAME original maps compose pointwise equally BEFORE true whole coherent pullback composition. -/
theorem actual_restricted_blowup_ideal_pullback {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (V : Opens Y) {I : GermIdeal n Y} (hI : I.IsCoherent) :
    GermIdeal.pullback (m := n) (Subtype.val : actualRestrictedBlowupOpen hπ V → Z)
      (GermIdeal.pullback (m := n) π I) =
    GermIdeal.pullback (m := n) (actualRestrictedBlowupMap hπ V)
      (GermIdeal.pullback (m := n) (Subtype.val : V → Y) I) := by
  rw [← GermIdealTotalTransform.pullback_comp hπ.contMDiff contMDiff_subtype_val hI,
    ← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val (actualRestrictedBlowupMap_holomorphic hπ V) hI]
  rfl

/-- TRUE original test history and domain internally supply every WHOLE ideal comparison over the actual open history. -/
theorem pullback_val_companionHistoryYearIdeal (hn : 0 < n) {m : MarkedIdeal n X} (h : IsInvDomain k m) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower m T →
      ∀ (U : Opens X) (q r : ℕ),
        GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y) (companionHistoryYearIdeal m T q r) =
          companionHistoryYearIdeal (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) q r
  | _, .refl, _, U, q, _ => pullback_val_companionYearBaselineIdeal hn h U q
  | _, .step T C π hπ, hT, U, q, r => by
    have ht := (isGeoTestTower_step_iff m T C π hπ).mp hT |>.1
    have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
    have hd' := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (.step T C π hπ) hT
    let V := openPreimage T U
    let W := openPreimage (.step T C π hπ) U
    let mU := MarkedIdeal.pullback (Subtype.val : U → X) m
    let J := geoTransformAlong m T
    let J' := geoTransformAlong m (.step T C π hπ)
    let Jq := nonmonomialOrderIdeal J (q+1)
    have hJq : Jq.IsCoherent := isCoherent_carrierOrderIdeal hd.isWellFormed.isClosedSubmanifold_N (actual_nm_coherent hn hd) (q+1)
    have hold := geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T ht
    have hnew := geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent (.step T C π hπ) hT
    cases r with
    | zero =>
      change GermIdeal.pullback (m := n) (Subtype.val : W → _) (sumIdeal (companionYearBaselineIdeal J' q)
        (GermIdeal.pullback (m := n) π Jq)) =
        sumIdeal (companionYearBaselineIdeal (geoTransformAlong mU (restrict U (.step T C π hπ))) q)
          (GermIdeal.pullback (m := n) (actualRestrictedBlowupMap hπ V)
            (nonmonomialOrderIdeal (geoTransformAlong mU (restrict U T)) (q+1)))
      rw [MarkedIdealOperationsTransform.pullback_sumIdeal contMDiff_subtype_val
        (hol_of_coherent (isCoherent_companionYearBaselineIdeal hn hd' q))
        (hol_of_coherent (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hJq)),
        pullback_val_companionYearBaselineIdeal hn hd' W q,hnew,hold,
        ← pullback_val_nonmonomialOrderIdeal hn hd V (q+1)]
      exact congrArg (sumIdeal _) (actual_restricted_blowup_ideal_pullback hπ V hJq)
    | succ r =>
      have hYear := isCoherent_companionHistoryYearIdeal hn h T ht q r
      have ih := pullback_val_companionHistoryYearIdeal hn h T ht U q r
      change GermIdeal.pullback (m := n) (Subtype.val : W → _) (sumIdeal (companionYearBaselineIdeal J' q)
        (GermIdeal.pullback (m := n) π (Jq.mul (companionHistoryYearIdeal m T q r)))) =
        sumIdeal (companionYearBaselineIdeal (geoTransformAlong mU (restrict U (.step T C π hπ))) q)
          (GermIdeal.pullback (m := n) (actualRestrictedBlowupMap hπ V)
            ((nonmonomialOrderIdeal (geoTransformAlong mU (restrict U T)) (q+1)).mul
              (companionHistoryYearIdeal mU (restrict U T) q r)))
      rw [MarkedIdealOperationsTransform.pullback_sumIdeal contMDiff_subtype_val
        (hol_of_coherent (isCoherent_companionYearBaselineIdeal hn hd' q))
        (hol_of_coherent (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff (IdealWeightPowers.isCoherent_mul hJq hYear))),
        pullback_val_companionYearBaselineIdeal hn hd' W q,hnew,hold,
        ← pullback_val_nonmonomialOrderIdeal hn hd V (q+1),← ih,
        ← GermIdealTotalTransform.pullback_mul contMDiff_subtype_val hJq hYear]
      exact congrArg (sumIdeal _) (actual_restricted_blowup_ideal_pullback hπ V (IdealWeightPowers.isCoherent_mul hJq hYear))

/-- Entire true carrier/ideal/ordered current boundary/mark record equality over the SAME actual original open history. -/
theorem pullback_val_companionHistoryYearMarked (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (ht : IsGeoTestTower m T)
    (U : Opens X) (q r : ℕ) :
    MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (companionHistoryYearMarked m T q r) =
      companionHistoryYearMarked (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) q r := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact preimage_univ
  · have hcurrent := geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T ht
    exact (congrArg (fun J => J.E) hcurrent).symm
  · exact pullback_val_companionHistoryYearIdeal hn h T ht U q r
  · rfl

/-- ONLY original canonical data internally supply every actual true source-test comparison. -/
theorem original_companionHistoryYearMarked_open_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (U : Opens X) (q r : ℕ) :
    MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (companionHistoryYearMarked m T q r) =
      companionHistoryYearMarked (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) q r :=
  pullback_val_companionHistoryYearMarked hn m h T
    ((invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc) U q r

end
end Hironaka.HironakaOriginalCoherentHistoryYearOpenNaturality
