import Hironaka.Resolution.HironakaG1NestedBareContactTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1AdvancingOrderZeroContact
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres TangentDirectionAlong ContactEquivalenceAlong
  CompanionRebase CompanionReductionAlong GeneralValue GeneralCompare NonmonomialOrderTail
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  HomogenizedIdealAlong CoefficientIdealRestriction RestrictedIdealExtension HomogenizedGlueingLiftAlong
  InvDomainTowerAlong InvDomainRebase ContactCanonicalAlong ContactRepresentative ContactStageKept
  StepOneValue StepOneRegime StepOneValueMasked
  HironakaG1NestedBareContactTransport HironakaG1ProperNormalZeroPhase
  HironakaCoherentTransformExtension RelativePrincipalizationSpan GermIdealPullbackCalculus HironakaG8LocalHistory
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 1900000 in
/-- Canonicality of Step One on the actual initial same-mark companion
gives canonicality and endpoint survival for the earlier prescribed
contact at the actual zero split, including genuinely advancing heads. -/
theorem order_companion_actual_zero_head_contact {n k : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain (k + 1) K) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hEq : companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X)) :
    let C := ordMask (geoTransformAlong K (.refl : BlowupTower X X)) K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
    let v : C → ℂ := u ∘ Subtype.val
    ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T →
      ∀ y ∈ (geoTransformAlong J T).cosupp,
      level J T y = 0 → (¬ IsSpecial J T y) →
      let r := regimeRun (stepRegime J 0) T y
      let H := head T r
      let S := tail T r
      let p := S.proj y
      let O := maskB J H p
      let D := contactMarkedKept Kc v H O
      let B := contactMarkedKept J v H O
      ∃ hp : p ∈ O,
        IsInvDomain k D ∧ IsCanonical D ((invFamily hn k).inv D) (restrict O S) ∧
        (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong D (restrict O S)).cosupp ∧
        RestrictEquiv B D ∧ D.N = (Subtype.val : O → _) ⁻¹' strictAlong H (Kc.N ∩ {x | v x = 0}) ∧
        D.d = (coeffMarkedAlong (geoTransformAlong (barMarked J) H)).d ∧
        D.E = (geoTransformAlong (barMarked J) H).E.map ((Subtype.val : O → _) ⁻¹' ·) ∧
        (∀ z ∈ (geoTransformAlong B (restrict O S)).cosupp,
          (invFamily hn k).inv B (restrict O S) z = (invFamily hn k).inv D (restrict O S) z) ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y =
          toLex (0, ((invFamily hn k).inv D (restrict O S) ⟨y, hp⟩ : WithTop (ValTy k))) := by
  intro C A J Kc v Y T hCan y hy hLevel hNS r H S p O D B
  let F := companionOf n K K.d
  have hF : F.IsWellFormed := HironakaG8E4cCompanion.companion_wf hK hn hK.one_le_d
  have hFJ : MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) F = J :=
    pullback_val_companionOf hn hK.isWellFormed hK.isNonzeroAlongAt C K.d
  have hJ : IsInvDomain (k + 1) J := isInvDomain_compAt hn hK.one_le_d (.refl : BlowupTower X X) hK
  have hKc : IsInvDomain (k + 1) Kc := isInvDomain_pullback_val C hK
  have hMax := isMaximalOrderAlong_compAt hn K.d (.refl : BlowupTower X X) hK
  have hFtan : IsTangentDirectionAlong F.N F.ideal F.d univ u := by
    unfold F
    rw [hEq]
    exact ⟨hu.isOpen, fun x hx =>
      iterDerivIdealAlong_mono (N := K.N) (le_restrictOn hK.isWellFormed.isCoherent)
        (K.d - 1) x u (hu.mem x hx), hu.multiplicity_one⟩
  have hv : IsTangentDirectionAlong J.N J.ideal J.d univ v := by
    rw [← hFJ]
    exact isTangentDirectionAlong_pullback_val C (hol_of_isCoherent hF.isCoherent)
      ⟨C.isOpen, fun x _ => hFtan.mem x (mem_univ x), fun x _ => hFtan.multiplicity_one x (mem_univ x)⟩
  obtain ⟨hp, hOwn, hB, hClass, _, _, _, _, _, hOwnCan, hBCan, hCos, hValue⟩ :=
    prescribed_contact_zero_phase hn J hJ hMax v hv T hCan y hy hLevel hNS
  let I := invFamily hn k
  have hTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical I J hJ hMax hn T hCan).1
  have hH := ((isGeoTestTower_iff_head_tail (barMarked J) T r).mp hTest).1
  have hRE : RestrictEquiv B D := initial_order_prescribed_contact_at_tested_head hn K hK u hEq H hH p
  have hFRE : RestrictEquiv F K := by
    unfold F
    rw [hEq]
    exact ⟨rfl, rfl, rfl, restrictLe_restrictOn, restrictLe_self_restrictOn hK.isWellFormed.isCoherent⟩
  have hJK : RestrictEquiv J Kc := by
    rw [← hFJ]
    exact restrictEquiv_pullback_val C hFRE hF.isCoherent hK.isWellFormed.isCoherent
  have hBar := restrictEquiv_barMarked hJK hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hKc.isWellFormed.isCoherent
  have hJB := isInvDomain_barMarked (X := A) J hJ
  have hKB := isInvDomain_barMarked (X := A) Kc hKc
  have hHK := ((RestrictEquiv.wEquiv hBar hJB.isWellFormed.isClosedSubmanifold_N.1
    hJB.isWellFormed.isCoherent hKB.isWellFormed.isCoherent).2 H).1.mp hH
  have hDCoh : D.ideal.IsCoherent :=
    isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff Kc hKc.isWellFormed.isCoherent hKc.isWellFormed.isClosedSubmanifold_N v H hHK)
  have hD : IsInvDomain k D := isInvDomain_of_restrictEquiv hB hRE hDCoh
  have hDCan := Seq.InvDomainRebase.isCanonical_of_restrictEquiv I hB hD hRE (restrict O S) hBCan
  have hCosEq := (RestrictEquiv.cosupp_admissible_geoTransformAlong hRE
    hB.isWellFormed.isClosedSubmanifold_N.1 hB.isWellFormed.isCoherent hDCoh (restrict O S)).1
  have hBD z (hz : z ∈ (geoTransformAlong B (restrict O S)).cosupp) :=
    I.isInvValue.representative B D hB hD hRE (restrict O S) hBCan z hz
  refine ⟨hp, hD, hDCan, hCosEq ▸ hCos, hRE, rfl, hRE.d_eq.symm, hRE.E_eq.symm, hBD, ?_⟩
  let P := lowerMarkedB J H p
  let z : openPreimage S O := ⟨y, hp⟩
  have hOwnTest := I.isInvValue.isGeoTestTower_of_isCanonical hOwn (restrict O S) hOwnCan
  have hOwnCos : z ∈ (geoTransformAlong P (restrict O S)).cosupp :=
    ((hClass.wEquiv.2 _).2 hOwnTest).symm ▸ hCos
  have hFinite := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial I J (lowerMarkedM J) T hNS
  rw [hLevel] at hFinite
  change _ = toLex (0, Seq.StepOneValueMasked.lowerValueL I J (lowerMarkedM J) 0 H S y) at hFinite
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem I J (lowerMarkedM J) (s := 0) (T₀ := H) (T₁ := S) (y := y) hp] at hFinite
  exact hFinite.trans (congrArg (fun x : ValTy k => toLex (0, (x : WithTop (ValTy k))))
    ((hValue z hOwnCos).trans (hBD z hCos)))

end
end Hironaka.HironakaG1AdvancingOrderZeroContact
