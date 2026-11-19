import Hironaka.Resolution.HironakaG1InitialBareContactCanonical
import Hironaka.Resolution.HironakaG1LocalizedBornNormalHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NestedBareContactTransport
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres TangentDirectionAlong ContactEquivalenceAlong
  CompanionRebase CompanionReductionAlong GeneralValue GeneralCompare NonmonomialOrderTail
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  HomogenizedIdealAlong CoefficientIdealRestriction RestrictedIdealExtension
  InvDomainTowerAlong InvDomainRebase ContactCanonicalAlong ContactRepresentative
  StepOneValue StepOneRegime StepOneValueMasked HironakaG1InitialBareContactCanonical
  HironakaSmoothSubmersionOrderedChoiceImageTrace GermIdealPullbackCalculus RelativePrincipalizationSpan
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 1500000 in
/-- A literal same-mark companion recodes the earlier bare coefficient record
on its exact order mask. Restriction through any further zero-phase mask
preserves the coefficient mark and the whole ordered boundary. -/
theorem nested_initial_bare_contact_data {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain k K) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hEq : companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X)) :
    let C := ordMask (geoTransformAlong K (.refl : BlowupTower X X)) K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let v : C → ℂ := u ∘ Subtype.val
    let D := withN (coeffMarkedAlong K) (K.N ∩ {x | u x = 0})
    let B := withN (coeffMarkedAlong J) (J.N ∩ {x | v x = 0})
    IsInvDomain l D →
    IsInvDomain k J ∧ IsTangentDirectionAlong J.N J.ideal J.d univ v ∧
      IsInvDomain l B ∧
      ∀ O : Opens A,
        let Z := CMfd.of (n := n) O
        let B' := MarkedIdeal.pullback (M' := Z) (Subtype.val : O → A) B
        let D' := MarkedIdeal.pullback (M' := Z) (fun z : O => z.val.val) D
        IsInvDomain l B' ∧ IsInvDomain l D' ∧ RestrictEquiv B' D' ∧
        D'.d = D.d ∧ D'.E = K.E.map ((fun z : O => z.val.val) ⁻¹' ·) := by
  intro C A J v D B hD
  let F := companionOf n K K.d
  let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
  have hF : F.IsWellFormed := HironakaG8E4cCompanion.companion_wf hK hn hK.one_le_d
  have hFJ : MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) F = J :=
    pullback_val_companionOf hn hK.isWellFormed hK.isNonzeroAlongAt C K.d
  have hJ : IsInvDomain k J :=
    isInvDomain_compAt hn hK.one_le_d (.refl : BlowupTower X X) hK
  have hFRE : RestrictEquiv K F := by
    unfold F
    rw [hEq]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hK.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hRE : RestrictEquiv Kc J := by
    rw [← hFJ]
    exact restrictEquiv_pullback_val C hFRE hK.isWellFormed.isCoherent hF.isCoherent
  have hKc : IsInvDomain k Kc := isInvDomain_pullback_val C hK
  have hFtan : IsTangentDirectionAlong F.N F.ideal F.d univ u := by
    unfold F
    rw [hEq]
    exact ⟨hu.isOpen, fun z hz => HomogenizedGlueingLiftAlong.iterDerivIdealAlong_mono
      (N := K.N) (le_restrictOn hK.isWellFormed.isCoherent) (K.d - 1) z u (hu.mem z hz),
      hu.multiplicity_one⟩
  have hJtan : IsTangentDirectionAlong J.N J.ideal J.d univ v := by
    rw [← hFJ]
    exact isTangentDirectionAlong_pullback_val C (hol_of_isCoherent hF.isCoherent)
      ⟨C.isOpen, fun x _ => hFtan.mem x (mem_univ x), fun x _ => hFtan.multiplicity_one x (mem_univ x)⟩
  have hP : MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) D =
      withN (coeffMarkedAlong Kc) (Kc.N ∩ {x | v x = 0}) := by
    change withN (MarkedIdeal.pullback (Subtype.val : C → X) (coeffMarkedAlong K))
      (Kc.N ∩ {x | v x = 0}) = _
    rw [pullback_val_coeffMarkedAlong C K hK.isWellFormed.isCoherent
      hK.isWellFormed.isClosedSubmanifold_N hK.one_le_d]
  have hDB : RestrictEquiv (MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) D) B := by
    rw [hP]
    have h := restrictEquiv_restrictedCoeff hRE (hol_of_isCoherent hKc.isWellFormed.isCoherent)
      (hol_of_isCoherent hJ.isWellFormed.isCoherent) (A := Kc.N ∩ {x | v x = 0}) inter_subset_left
    unfold B
    simpa only [hRE.N_eq] using h
  have hDc := isInvDomain_pullback_val C hD
  have hBCoh : B.ideal.IsCoherent := isCoherent_coeffMarkedAlong
    hJ.isWellFormed.isCoherent hJ.isWellFormed.isClosedSubmanifold_N
  have hB : IsInvDomain l B := isInvDomain_of_restrictEquiv hDc hDB hBCoh
  refine ⟨hJ, hJtan, hB, fun O => ?_⟩
  intro Z B' D'
  have hFlat : D' = MarkedIdeal.pullback (M' := Z) (Subtype.val : O → A)
      (MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) D) :=
    whole_markedPullback_comp contMDiff_subtype_val contMDiff_subtype_val D hD.isWellFormed.isCoherent
  refine ⟨isInvDomain_pullback_val O hB, ?_, ?_, rfl, rfl⟩
  · rw [hFlat]
    exact isInvDomain_pullback_val O hDc
  · rw [hFlat]
    exact restrictEquiv_pullback_val O (restrictEquiv_symm hDB) hBCoh hDc.isWellFormed.isCoherent

set_option maxHeartbeats 1800000 in
/-- The actual zero-mask canonical suffix of the initial same-mark order
companion is canonical for the earlier prescribed bare contact on the very
same restricted tower, at its original recursive coefficient mark. -/
theorem initial_order_zero_canonical_for_earlier_contact {n k : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain (k + 1) K) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hEq : companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X)) :
    let C := ordMask (geoTransformAlong K (.refl : BlowupTower X X)) K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let D := withN (coeffMarkedAlong K) (K.N ∩ {x | u x = 0})
    IsInvDomain k D →
    ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T →
      ∀ y ∈ (geoTransformAlong J T).cosupp,
      level J T y = 0 → (¬ IsSpecial J T y) → regimeRun (stepRegime J 0) T y = T.length →
      let O := maskB J (.refl : BlowupTower A A) (T.proj y)
      let D' := MarkedIdeal.pullback (fun z : O => z.val.val) D
      ∃ hp : T.proj y ∈ O,
        IsCanonical D' ((invFamily hn k).inv D') (restrict O T) ∧
        (⟨y, hp⟩ : openPreimage T O) ∈ (geoTransformAlong D' (restrict O T)).cosupp ∧
        D'.d = D.d ∧ D'.E = K.E.map ((fun z : O => z.val.val) ⁻¹' ·) := by
  intro C A J D hD Y T hCan y hy hl hNS hRun O D'
  let v : C → ℂ := u ∘ Subtype.val
  let B := withN (coeffMarkedAlong J) (J.N ∩ {x | v x = 0})
  let B' := MarkedIdeal.pullback (Subtype.val : O → A) B
  obtain ⟨hJ, hv, hB, hNested⟩ := nested_initial_bare_contact_data (l := k) hn K hK u hu hEq hD
  have hMax := isMaximalOrderAlong_compAt hn K.d (.refl : BlowupTower X X) hK
  obtain ⟨hp, hBCan, hBCos⟩ :=
    initial_zero_stepOne_bare_contact_canonical hn J hJ hMax v hv T hCan y hy hl hNS hRun hB
  obtain ⟨hB', hD', hRE, hd, hE⟩ := hNested O
  have hDCan := Seq.InvDomainRebase.isCanonical_of_restrictEquiv (invFamily hn k)
    hB' hD' hRE (restrict O T) hBCan
  have hCos := (RestrictEquiv.cosupp_admissible_geoTransformAlong hRE
    hB'.isWellFormed.isClosedSubmanifold_N.1 hB'.isWellFormed.isCoherent hD'.isWellFormed.isCoherent
    (restrict O T)).1
  exact ⟨hp, hDCan, hCos ▸ hBCos, hd, hE⟩


open ContactStageKept

set_option maxHeartbeats 1250000 in
/-- The earlier prescribed representative and the actual initial
same-mark companion give the same restricted contact at every tested
zero-phase head, with the exact companion mask and stage boundary. -/
theorem initial_order_prescribed_contact_at_tested_head {n k : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain k K) (u : X → ℂ)
    (hEq : companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X)) :
    let C := ordMask (geoTransformAlong K (.refl : BlowupTower X X)) K.d
    let A := CMfd.of (n := n) C
    let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
    let J := compAt K K.d (.refl : BlowupTower X X)
    let v : C → ℂ := u ∘ Subtype.val
    ∀ {Y : CMfd.{0} n} (H : BlowupTower A Y), IsGeoTestTower (barMarked J) H →
    ∀ a : Y,
      let O := maskB J H a
      RestrictEquiv (contactMarkedKept J v H O) (contactMarkedKept Kc v H O) := by
  intro C A Kc J v Y H hH a O
  let F := companionOf n K K.d
  have hF : F.IsWellFormed := HironakaG8E4cCompanion.companion_wf hK hn hK.one_le_d
  have hFJ : MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) F = J :=
    pullback_val_companionOf hn hK.isWellFormed hK.isNonzeroAlongAt C K.d
  have hFRE : RestrictEquiv F K := by
    unfold F
    rw [hEq]
    exact ⟨rfl, rfl, rfl, restrictLe_restrictOn, restrictLe_self_restrictOn hK.isWellFormed.isCoherent⟩
  have hRE : RestrictEquiv J Kc := by
    rw [← hFJ]
    exact restrictEquiv_pullback_val C hFRE hF.isCoherent hK.isWellFormed.isCoherent
  have hJ : IsInvDomain k J := isInvDomain_compAt hn hK.one_le_d (.refl : BlowupTower X X) hK
  have hKc : IsInvDomain k Kc := isInvDomain_pullback_val C hK
  exact restrictEquiv_contactMarkedKept hJ.isWellFormed.isCoherent hKc.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hRE ⊤ (u := v) (w := v) (fun _ _ _ => rfl)
    H hH O (fun _ _ => trivial)

end
end Hironaka.HironakaG1NestedBareContactTransport
