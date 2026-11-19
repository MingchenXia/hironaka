import Hironaka.Resolution.HironakaG1RecursiveBornOrderExample

/-! The next literal selected record in the canonical recursive-born example. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RecursiveBornSelectedExample
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  GeneralValue NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1LaterPositiveNormalExample HironakaG1RecursiveBornFiniteExample
  HironakaG1RecursiveBornOrderExample HironakaG1InitialPositiveGeneralRead
  HironakaG1PositiveNormalNonspecialExample StepOneValue StepOneValueMasked
  StepOneLowerDomain BoundaryCount MarkedIdealBiholomorphism InvDomainMemberRestriction
  InvDomainRebase HomogenizedIdealAlong CoefficientIdeal

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev F : Set Y := π ⁻¹' ({p} : Set X)
private abbrev A := geoTransformAlong record B
private abbrev W := ordMask (M := Y) A 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J : MarkedIdeal 3 V := compAt record 1 B
private abbrev R : BlowupTower V V := .refl
private abbrev D : Set W := (Subtype.val : W → Y) ⁻¹' F
private abbrev O (z : W) := maskA J R z
private abbrev L (z : W) := lowerMarkedM J 1 R z

private theorem J_boundary : J.E = [D] := by
  simp only [J, compAt, companionOf, companionAlong_E]
  change A.E.map ((Subtype.val : W → Y) ⁻¹' ·) = _
  rw [stage_boundary]
  rfl

private theorem J_carrier : J.N = univ := by
  simp only [J, compAt, companionOf, companionAlong_N]
  change (Subtype.val : W → Y) ⁻¹' A.N = univ
  rw [stage_carrier, preimage_univ]

private theorem selected_geometry (z : W) (hJ : IsInvDomain 3 J) (hd : J.d = 1)
    (hLev : level J R z = 1) :
    (L z).N = (Subtype.val : O z → W) ⁻¹' D ∧ (L z).E = [] ∧ (L z).d = 1 := by
  have hD : z ∈ D := by
    change boundaryCount (J.E.take J.E.length) z = 1 at hLev
    rw [List.take_length, J_boundary] at hLev
    by_contra hz
    simp [boundaryCount, hz] at hLev
  have hBar : barMarked J = J := by
    change coeffMarkedAlong (homMarkedAlong J) = J
    rw [homMarkedAlong_eq_of_mark_one J hd hJ.isWellFormed.isCoherent,
      coeffMarkedAlong_eq_of_mark_one J hd hJ.isWellFormed.isCoherent]
  let K := memberRestrict J (membersThrough J.E J.E z)
  have hkN : K.N = D := by
    change (memberRestrict J (membersThrough J.E J.E z)).N = D
    rw [memberRestrict_membersThrough_N, J_carrier, J_boundary]
    ext u
    simp [hD]
  have hkE : K.E = [] := by
    change (memberRestrict J (membersThrough J.E J.E z)).E = []
    rw [memberRestrict_membersThrough_E, J_boundary]
    simp [hD]
  have hkD : K.d = 1 := by
    change (coeffMarkedAlong J).d = 1
    rw [coeffMarkedAlong_eq_of_mark_one J hd hJ.isWellFormed.isCoherent, hd]
  have hK : L z = MarkedIdeal.pullback (Subtype.val : O z → W) K := by
    unfold L lowerMarkedM lowerMarked
    simp only [geoTransformAlong_refl, show origMembers J R = J.E from List.take_length]
    exact congrArg (fun Q : MarkedIdeal 3 V =>
      MarkedIdeal.pullback (Subtype.val : O z → W) (memberRestrict Q (membersThrough Q.E J.E z))) hBar
  rw [hK]
  exact ⟨congrArg (fun N : Set W => (Subtype.val : O z → W) ⁻¹' N) hkN,
    congrArg (List.map ((Subtype.val : O z → W) ⁻¹' ·)) hkE, hkD⟩

set_option maxHeartbeats 600000 in
/-- The genuine finite inner value is the original invariant on the exact
level-one selected trace of the born divisor, with no remaining boundary. -/
theorem actual_selected_born_read :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let T := BlowupTower.refl (X := CMfd.of (n := 3) (O z))
      let v := (invFamily (by decide : 0 < 3) 2).inv (L z) T (⟨z, hz⟩ : O z)
      (L z).N = (Subtype.val : O z → W) ⁻¹' D ∧ (L z).E = [] ∧ (L z).d = 1 ∧
      (invFamily (by decide : 0 < 3) 3).inv record B q =
        positiveSuccessorRead 1 (toLex (1, (v : WithTop (ValTy 2)))) := by
  obtain ⟨hq, v, hMark, hNS, hVal, hRead⟩ := actual_finite_positive_companion
  obtain ⟨hq', hJ, _, hLev, _⟩ := actual_positive_companion_level
  have hLev : level J R (⟨q, hq⟩ : W) = 1 := hLev
  let z : W := ⟨q, hq⟩
  have hz : z ∈ O z := mem_maskA (X := V) J hJ.isWellFormed hJ.one_le_d (by decide) R
    trivial hLev.ge hNS
  let R₂ := invFamily (by decide : 0 < 3) 2
  let T := BlowupTower.refl (X := CMfd.of (n := 3) (O z))
  have hInner : Seq.StepOneValueMasked.stepOneInvM R₂ J R z =
      toLex (1, (R₂.inv (L z) T (⟨z, hz⟩ : O z) : WithTop (ValTy 2))) := by
    change Seq.StepOneValueMasked.stepOneInvL R₂ J (lowerMarkedM J) R z = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R₂ J (lowerMarkedM J) R hNS, hLev]
    change toLex (1, Seq.StepOneValueMasked.lowerValueL R₂ J (lowerMarkedM J) 1 R R z) = _
    unfold Seq.StepOneValueMasked.lowerValueL
    rw [dif_pos (show R.proj z ∈ lowerMask J 1 R (R.proj z) from hz)]
    rfl
  obtain ⟨hN, hE, hd⟩ := selected_geometry z hJ hMark hLev
  refine ⟨hq, hz, hN, hE, hd, ?_⟩
  exact hRead.trans (congrArg (positiveSuccessorRead 1) (hVal.symm.trans hInner))

end
end Hironaka.HironakaG1RecursiveBornSelectedExample
