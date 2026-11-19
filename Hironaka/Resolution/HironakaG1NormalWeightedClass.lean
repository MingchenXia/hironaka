import Hironaka.Resolution.HironakaG1ProperCarrierNormalLocalClass
import Hironaka.Resolution.HironakaG8LocalPower

/-!
# Common whole powers on a fixed proper normal chart

The section pullback detects the source whole powers of padded presentations.
For source records with the same carrier and ordered boundary, equality of
those powers at the common mark gives equality of local test classes, including
tests with a list of extra ambient boundary members.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NormalWeightedClass

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealPullbackCalculus IdealWeightPowers
  MarkedIdeals BlowupTowers ResolutionInvariantSpec MarkedIdealOperationsAlong.MarkedIdeal
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaSmoothSubmersionCoefficientIdeals HironakaRelativeNormalIdeal
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaActualPowerBoundaryExponents
  HironakaG8LocalHistory HironakaG8LocalPower HironakaG8ClassStepCut HironakaG8LocalContactStage

variable {n k l : ℕ} {U : Opens (ComplexModel n)}

private theorem projection_section (U : Opens (ComplexModel n)) :
    projection U ∘ zeroSection U = id := by
  funext x
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

/-- The literal section pullback of a padded whole power retains all fields of
the source power, including its proper carrier and native rescaled mark. -/
theorem markedPullback_power_properNormal (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (e : ℕ) :
    markedPullback (m := n) (zeroSection U) (powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) e) =
      powerMarked (X := CMfd.of (n := n) U) Q e := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · change zeroSection U ⁻¹' (projection U ⁻¹' Q.N) = Q.N
    rw [← Set.preimage_comp, projection_section]
    rfl
  · change (Q.E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·) = Q.E
    rw [List.map_map]
    change Q.E.map (fun H => (projection U ∘ zeroSection U) ⁻¹' H) = Q.E
    rw [projection_section]
    exact List.map_id Q.E
  · change GermIdeal.pullback (m := n) (zeroSection U) (idealPow (properNormalMarked Q).ideal e) =
      idealPow Q.ideal e
    rw [pullback_idealPow (zeroSection_contMDiff U)
      (properNormalMarked_isInvDomain Q hQ).isWellFormed.isCoherent]
    have hTrace := entire_relative_derivative_trace hQ.isWellFormed.isClosedSubmanifold_N
      hQ.isWellFormed.isCoherent (d := Q.d) (j := 0) hQ.one_le_d
    change GermIdeal.pullback (m := n) (zeroSection U) (properNormalMarked Q).ideal = Q.ideal at hTrace
    rw [hTrace]

private theorem power_sectionMarked (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (e : ℕ) :
    powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (sectionMarked Q) e = sectionMarked (powerMarked (X := CMfd.of (n := n) U) Q e) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change idealPow (GermIdeal.pullback (m := n + 1) (projection U) Q.ideal) e =
    GermIdeal.pullback (m := n + 1) (projection U) (idealPow Q.ideal e)
  exact (pullback_idealPow (projection_contMDiff U) hQ.isWellFormed.isCoherent e).symm

private theorem sectionMarked_isInvDomain (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    IsInvDomain k (sectionMarked Q) :=
  section_projected_domain k Q.N Q.E Q.ideal Q.d hQ

private theorem sectionMarked_restrictEquiv {P Q : MarkedIdeal n U}
    (hP : P.ideal.IsCoherent) (hQ : Q.ideal.IsCoherent) (h : RestrictEquiv P Q) :
    RestrictEquiv (sectionMarked P) (sectionMarked Q) := by
  refine ⟨congrArg liftedCarrier h.N_eq, congrArg (List.map (projection U ⁻¹' ·)) h.E_eq,
    h.d_eq, ?_, ?_⟩
  · exact HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
      (projection_contMDiff U) (fun _ hx => hx.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQ hg) h.le
  · exact HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
      (projection_contMDiff U) (fun _ hx => hx.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP hg) h.ge

/-- Restricted equivalence on the actual zero section is equivalent to
restricted equivalence of the original records. -/
theorem sectionMarked_restrictEquiv_iff {P Q : MarkedIdeal n U}
    (hP : P.ideal.IsCoherent) (hQ : Q.ideal.IsCoherent) :
    RestrictEquiv (sectionMarked P) (sectionMarked Q) ↔ RestrictEquiv P Q := by
  refine ⟨?_, sectionMarked_restrictEquiv hP hQ⟩
  intro h
  have hMem (A : Set U) (x : U) : zeroSection U x ∈ liftedCarrier A ↔ x ∈ A := by
    change (projection U (zeroSection U x) ∈ A ∧ _) ↔ x ∈ A
    have hRet : projection U (zeroSection U x) = x := congrFun (projection_section U) x
    rw [hRet]
    simp [zeroSection]
  have hN : P.N = Q.N := by
    ext x
    rw [← hMem P.N x, ← hMem Q.N x]
    exact Set.ext_iff.mp h.N_eq _
  have hE : P.E = Q.E := by
    have hLists := congrArg (List.map (zeroSection U ⁻¹' ·)) h.E_eq
    have hIdent (E : List (Set U)) :
        (E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·) = E := by
      rw [List.map_map]
      change E.map (fun H => (projection U ∘ zeroSection U) ⁻¹' H) = E
      rw [projection_section]
      exact List.map_id E
    change (P.E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·) =
      (Q.E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·) at hLists
    simpa only [hIdent] using hLists
  have hIdeal {I : GermIdeal n U} (hI : I.IsCoherent) :
      GermIdeal.pullback (m := n) (zeroSection U)
        (GermIdeal.pullback (m := n + 1) (projection U) I) = I := by
    rw [← HironakaSmoothSubmersionOrderedChoiceImageTrace.coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U) I hI,
      projection_section, BlowupControlledTransform.pullback_id hI]
  refine ⟨hN, hE, h.d_eq, ?_, ?_⟩
  · have hLe := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
      (zeroSection_contMDiff U) (fun x hx => (hMem P.N x).mpr hx)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
        (isCoherent_pullback (projection_contMDiff U) hQ) hg) h.le
    simpa only [sectionMarked, hIdeal hP, hIdeal hQ] using hLe
  · have hGe := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
      (zeroSection_contMDiff U) (fun x hx => (hMem P.N x).mpr hx)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
        (isCoherent_pullback (projection_contMDiff U) hP) hg) h.ge
    simpa only [sectionMarked, hIdeal hP, hIdeal hQ] using hGe

/-- At a common positive powered mark, the restricted ideals on the proper
source carrier determine the padded local class, with the extra ambient
boundary retained. -/
theorem restrictEquiv_commonPower_properNormal_locWPEquiv (P Q : MarkedIdeal n U)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) (hPow : RestrictEquiv
      (powerMarked (X := CMfd.of (n := n) U) P e) (powerMarked (X := CMfd.of (n := n) U) Q f))
    (F : List (Set (productOpen U))) :
    LocWPEquiv (X := CMfd.of (n := n + 1) (productOpen U))
      { powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked P) e with E := F ++ (properNormalMarked P).E }
      { powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) f with E := F ++ (properNormalMarked Q).E } := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  have hP' : LocWPEquiv (X := X) (powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked P) e)
      (powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (sectionMarked P) e) :=
    locEquiv_pow rfl (properNormalMarked_locWPEquiv_section P hP)
      (properNormalMarked_isInvDomain P hP) (sectionMarked_isInvDomain P hP) he he
  have hQ' : LocWPEquiv (X := X) (powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) f)
      (powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (sectionMarked Q) f) :=
    locEquiv_pow rfl (properNormalMarked_locWPEquiv_section Q hQ)
      (properNormalMarked_isInvDomain Q hQ) (sectionMarked_isInvDomain Q hQ) hf hf
  have hPS := sectionMarked_isInvDomain _ (powerMarked_isInvDomain (X := CMfd.of (n := n) U) P hP he)
  have hQS := sectionMarked_isInvDomain _ (powerMarked_isInvDomain (X := CMfd.of (n := n) U) Q hQ hf)
  have hRes := sectionMarked_restrictEquiv
    (powerMarked_isInvDomain (X := CMfd.of (n := n) U) P hP he).isWellFormed.isCoherent
    (powerMarked_isInvDomain (X := CMfd.of (n := n) U) Q hQ hf).isWellFormed.isCoherent hPow
  have hSection : LocWPEquiv (X := X) _ _ :=
    locEquiv_of_restrictEquiv_closed (κ := Kinds.wp) rfl hRes
      hPS.isWellFormed.isClosedSubmanifold_N hPS.isWellFormed.isCoherent hQS.isWellFormed.isCoherent
  rw [power_sectionMarked P hP] at hP'
  rw [power_sectionMarked Q hQ] at hQ'
  have h := hP'.trans (hSection.trans hQ'.symm)
  have hE := h.E_eq
  exact hE ▸ locEquiv_addE (κ := Kinds.wp) rfl h F


/-- Equality of two positive common powers of the source records suffices for
the fixed-chart comparison. The ordinary normal cylinder is kept through the
comparison, and the new boundary list lives in the actual enlarged ambient. -/
theorem commonPower_properNormal_locWPEquiv (P Q : MarkedIdeal n U)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) (hPow : powerMarked (X := CMfd.of (n := n) U) P e = powerMarked (X := CMfd.of (n := n) U) Q f)
    (F : List (Set (productOpen U))) :
    LocWPEquiv (X := CMfd.of (n := n + 1) (productOpen U))
      { powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked P) e with E := F ++ (properNormalMarked P).E }
      { powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) f with E := F ++ (properNormalMarked Q).E } := by
  apply restrictEquiv_commonPower_properNormal_locWPEquiv P Q hP hQ he hf _ F
  rw [hPow]
  exact RestrictEquiv.refl
    (powerMarked_isInvDomain (X := CMfd.of (n := n) U) Q hQ hf).isWellFormed.isCoherent

/-- With extra ambient boundary members present, the rescaled padded cosupport
is still the image of the original cosupport under the actual zero section. -/
theorem power_properNormal_cosupp (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {e : ℕ} (he : 1 ≤ e) (F : List (Set (productOpen U))) :
    ({ powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) e with
      E := F ++ (properNormalMarked Q).E } : MarkedIdeal (n + 1) (productOpen U)).cosupp =
      zeroSection U '' Q.cosupp := by
  exact (powerMarked_cosupp (X := CMfd.of (n := n + 1) (productOpen U))
    (properNormalMarked Q) (properNormalMarked_isInvDomain Q hQ) he).trans
      (properNormalMarked_cosupp Q hQ)

/-- Every common fixed-chart test has the same admissibility in both
directions when the source powers at the common mark agree. -/
theorem commonPower_properNormal_test_iff (P Q : MarkedIdeal n U)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f)
    (hPow : powerMarked (X := CMfd.of (n := n) U) P e =
      powerMarked (X := CMfd.of (n := n) U) Q f)
    (F : List (Set (productOpen U))) {m : ℕ} {Y : CMfd.{0} m} {E : List (Set Y)}
    (H : LHist (CMfd.of (n := n + 1) (productOpen U)) (F ++ (properNormalMarked P).E) Y E)
    (hH : LHist.InKinds Kinds.wp H) :
    LHist.IsTest
      { powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked P) e with
        E := F ++ (properNormalMarked P).E } H ↔
    LHist.IsTest
      { powerMarked (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) f with
        E := F ++ (properNormalMarked P).E } H := by
  have h := commonPower_properNormal_locWPEquiv P Q hP hQ he hf hPow F
  exact h.isTest_iff H hH

end

end Hironaka.HironakaG1NormalWeightedClass
