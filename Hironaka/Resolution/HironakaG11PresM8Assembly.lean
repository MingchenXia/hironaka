import Hironaka.Resolution.HironakaG11PresM8EmptyPad

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Plan module 8 for the padded family: the maximal-order value function (repair (B'))

Blueprint: `hironaka-g11-pres-m8-empty-prefix.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d (target
`isMaxOrderValue_stepOneInvBM_pad`); lane G11B (inbox I-1368, comment C-0004) asked lane G11C to write this assembly if G11B's
run had ended when field (4') landed (G11B REPORT-r7, 32daf0b1c2).

* **`isMaxOrderValue_stepOneInvBM_pad`**: `MaxOrderValue.IsMaxOrderValue n k (fun 𝔍 T y => stepOneInvBM (Rm 𝔍.E.length) 𝔍 T y)`
  for a family `Rm` with `hfam` and the independence of the hypersurface of maximal contact (`TangentIndepBM`, plan module 6).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11PresM8Assembly

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneValueMasked Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.BlowupTowerIsomorphism
  Hironaka.BlowupTowerIsoTail Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMCanonicalTail Hironaka.HironakaG11InvBMAdmissible
  Hironaka.HironakaG11InvBMTangentIndep Hironaka.HironakaG11InvBMNaturality
  Hironaka.HironakaG11InvBMRestrictOpen
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.CoefficientIdealRestriction (withN)
open Hironaka.HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open Hironaka.RestrictedIdealWeight (RestrictLe)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv hol_of_isCoherent)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Plan module 8 for the padded family: Bierstone--Milman's Step 1 value is a maximal-order value function**
(BPRIME-PLAN §6d): for a family `Rm` of resolution invariants in dimension `≤ k - 1` with `(Rm (m + m')).inv L = (Rm m).inv
(padE L m')` and the independence of the hypersurface of maximal contact for every marked ideal of the domain of maximal order
with `Rm |𝔍.E|`, the value `𝔍 ↦ stepOneInvBM (Rm |𝔍.E|) 𝔍` has the properties (1)--(7), (4') of a maximal-order value function
(`0 < n`). Fields (1)--(4): lane G11B's `HironakaG11InvBMBridge`; (5), (6), (7): G11B's `HironakaG11InvBMRestrictOpen`,
`HironakaG11InvBMTowerIso`, `HironakaG11InvBMRepresentative`; (4'): `HironakaG11PresM8EmptyPad.emptyPrefix_field`. The proof
of the fields (1)--(3), (5)--(7) is lane G11B's draft (`work/hironaka-resume-20261111/G11B/drafts/HironakaG11InvBMMaxOrder.lean`). -/
theorem isMaxOrderValue_stepOneInvBM_pad (Rm : ℕ → ResolutionInvariant.{u, v} n (k - 1) Λ) (hn : 0 < n)
    (hfam : ∀ (m m' : ℕ) {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
      (Rm (m + m')).inv L T y = (Rm m).inv (HironakaG11InvBMPad.padE L m') T y)
    (hTI : ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      TangentIndepBM 𝔍 (Rm 𝔍.E.length)) :
    MaxOrderValue.IsMaxOrderValue n k (fun {X} 𝔍 {Y} T y => stepOneInvBM (X := X) (Rm 𝔍.E.length) 𝔍 (Y := Y) T y) where
  admissible := by
    intro X 𝔍 h hmax Y T hcan W l hle
    exact HironakaG11InvBMBridge.admissible_field _ 𝔍 (anchorChangeBM_of_tangentIndepBM 𝔍 _ (hTI 𝔍 h hmax)) h hmax hn T
      hcan W l hle
  usc := by
    intro X 𝔍 h hmax Y T hcan
    exact HironakaG11InvBMBridge.usc_field _ 𝔍 (anchorChangeBM_of_tangentIndepBM 𝔍 _ (hTI 𝔍 h hmax)) h hmax hn T hcan
  decrease := by
    intro X 𝔍 h hmax Y Z T C π hπ hcan hC
    exact HironakaG11InvBMBridge.decrease_field _ 𝔍 (anchorChangeBM_of_tangentIndepBM 𝔍 _ (hTI 𝔍 h hmax)) h hmax hn T C π
      hπ hcan hC
  emptyStep := by
    intro X 𝔍 h hmax Y Z T C π hπ hC hcan
    exact HironakaG11InvBMBridge.emptyStep_field _ 𝔍 (anchorChangeBM_of_tangentIndepBM 𝔍 _ (hTI 𝔍 h hmax)) h hmax hn T C π
      hπ hC hcan
  emptyPrefix := by
    intro X 𝔍 h hmax Y₀ Y T₀ T₁ h₀ hcan
    refine HironakaG11PresM8EmptyPad.emptyPrefix_field 𝔍 Rm hfam h hmax hn (hTI 𝔍 h hmax) (fun P hP => ?_) T₀ T₁ h₀ hcan
    exact hTI _ (InvDomainRebase.isInvDomain_geoTransformAlong_of_isEmptyTower h P hP)
      (StepOneEmptyPrefix.hypotheses_emptyPrefix 𝔍 h.isWellFormed h.one_le_d hmax h.dimLE P hP).2.2.1
  restrictOpen := by
    intro X 𝔍 h hmax U Y T hcan p hp
    have hU := InvDomainTowerAlong.isInvDomain_pullback_val U h
    have hmaxU := (StepOneRestrictOpen.hypotheses_restrict 𝔍 U h.isWellFormed h.one_le_d hmax h.dimLE).2.2.1
    have hlen : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).E.length = 𝔍.E.length := List.length_map _
    have hTIU : TangentIndepBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (Rm (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).E.length) := hTI _ hU hmaxU
    rw [hlen] at hTIU ⊢
    exact HironakaG11InvBMRestrictOpen.restrictOpen_field U _ 𝔍 h hmax hn (hTI 𝔍 h hmax) hTIU T hcan p hp
  towerIso := by
    intro X X' Φ 𝔍 h hmax Y' Y T' T χ hiso hcan p hp
    have h' := InvDomainTowerAlong.isInvDomain_pullback Φ h
    have hmax' := (StepOneTowerIso.hypotheses_pullback Φ 𝔍 h.isWellFormed h.one_le_d hmax h.dimLE).2.2.1
    have hlen : (MarkedIdeal.pullback Φ 𝔍).E.length = 𝔍.E.length := List.length_map _
    have hTI' : TangentIndepBM (MarkedIdeal.pullback Φ 𝔍) (Rm (MarkedIdeal.pullback Φ 𝔍).E.length) := hTI _ h' hmax'
    rw [hlen] at hTI' ⊢
    exact HironakaG11InvBMTowerIso.towerIso_field Φ _ 𝔍 h hmax hn (hTI 𝔍 h hmax) hTI' T' T χ hiso hcan p hp
  representative := by
    intro X 𝔍 𝔫 h hmax h𝔫 hmax𝔫 hEq Y T hcan y hy
    have hlen : 𝔫.E.length = 𝔍.E.length := by rw [hEq.E_eq]
    have hTI' : TangentIndepBM 𝔫 (Rm 𝔫.E.length) := hTI 𝔫 h𝔫 hmax𝔫
    rw [hlen] at hTI' ⊢
    exact HironakaG11InvBMRepresentative.representative_field _ h hmax h𝔫 hmax𝔫 hn hEq (hTI 𝔍 h hmax) hTI' T hcan y hy

end

end Hironaka.HironakaG11PresM8Assembly
