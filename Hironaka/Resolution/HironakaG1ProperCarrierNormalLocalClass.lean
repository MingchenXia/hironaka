import Hironaka.Resolution.HironakaG1ProperCarrierNormalContact
import Hironaka.Resolution.HironakaActualSectionMemberRestriction
import Hironaka.Resolution.HironakaActualOpenSectionRepresentative
import Hironaka.Resolution.HironakaG8LocalContactStage
import Hironaka.Resolution.HironakaG8HomStable
import Hironaka.Resolution.HironakaCoherentTransformExtension

/-! Actual kept normal coefficient/test dictionary on proper original carriers.
Blueprint FIRST: hironaka-g1-proper-carrier-normal-local-class.tex.
Every original boundary slot and true coefficient mark is retained.
No numerical, canonical or independent-history correspondence is assumed. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperCarrierNormalLocalClass
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
  RestrictedIdealExtension CoefficientIdealRestriction IdealOrderArithmetic IdealWeightPowers CoefficientIdeal
  DerivativeIdealAlong DerivativeIdealAlongCoherent HomogenizedIdealAlong HomogenizedGlueing
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  BlowupTowers ResolutionInvariantSpec StepOneValue TangentDirectionAlong
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualRelativeNormalGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaActualSectionMemberRestriction HironakaActualOpenSectionRepresentative
  HironakaRelativeNormalIdeal HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalContact HironakaG8LocalHistory HironakaG8LocalContact
  HironakaG8LocalContactStage HironakaG8HomStable HironakaG8CoefficientBoundaryLocal
  HironakaCoherentTransformExtension

variable {n k : ℕ} {U : Opens (ComplexModel n)}

private theorem hol {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {I : GermIdeal m Y} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt m f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

/-- The actual section-supported original representative, distinct from its cylinder. -/
def sectionMarked (Q : MarkedIdeal n U) : MarkedIdeal (n+1) (productOpen U) :=
  ⟨liftedCarrier Q.N,Q.E.map (projection U ⁻¹' ·),
    GermIdeal.pullback (m:=n+1) (projection U) Q.ideal,Q.d⟩

/-- Actual kept normal lower of the ORIGINAL padded bar; no boundary deletion. -/
def keptNormalLower (Q : MarkedIdeal n U) : MarkedIdeal (n+1) (productOpen U) :=
  withN (coeffMarkedAlong (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) (properNormalMarked Q)))
    (liftedCarrier Q.N)

/-- Actual coefficient of the ORIGINAL bar of the genuine section record. -/
def sectionBarCoefficient (Q : MarkedIdeal n U) : MarkedIdeal (n+1) (productOpen U) :=
  coeffMarkedAlong (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) (sectionMarked Q))

private theorem section_domain (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    IsInvDomain k (sectionMarked Q) := by
  exact HironakaActualSectionBoundaryGeometry.section_projected_domain k Q.N Q.E Q.ideal Q.d hQ

/-- The ACTUAL original padded bar contains the power at its TRUE native mark. -/
theorem normal_power_mem_bar (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (x : productOpen U) :
    (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) (properNormalMarked Q)).ideal.mem x
      (fun z=>relativeNormalCoordinate U z^
        (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) (properNormalMarked Q)).d) := by
  let P:=properNormalMarked Q
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hd : 0<Q.d:=hQ.one_le_d
  refine coeffMarkedAlong_normal_power_mem (homMarkedAlong P) hd (fun y => ?_) x
  change (homMarkedAlong P).ideal.mem y (fun z => relativeNormalCoordinate U z ^ Q.d)
  apply le_homogenizedIdealAlong (hol hP.isWellFormed.isCoherent) hP.one_le_d y
  simpa only [properNormalMarked, Nat.add_zero, iterDerivIdealAlong] using
    normal_power_relative_member U Q.N Q.ideal Q.d 0 y

/-- Actual normal tangent at the TRUE original bar mark, produced from ordinary Q. -/
theorem bar_normal_tangent (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    IsTangentDirectionAlong (properNormalMarked Q).N
      (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) (properNormalMarked Q)).ideal
      (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) (properNormalMarked Q)).d univ
      (relativeNormalCoordinate U) := by
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hB:=isInvDomain_barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) (properNormalMarked Q) hP
  exact normal_tangent_of_power_member U Q.N _ hB.isWellFormed.isCoherent _ hB.one_le_d
    (normal_power_mem_bar Q hQ)

private theorem contact_carrier (Q : MarkedIdeal n U) :
    (properNormalMarked Q).N∩{z|relativeNormalCoordinate U z=0}∩univ=liftedCarrier Q.N := by
  ext z
  change ((projection U z∈Q.N∧relativeNormalCoordinate U z=0)∧z∈univ)↔
    (projection U z∈Q.N∧HironakaActualCentreJointJets.actualJointNormalProjection n 1 z.val=0)
  have hcoord : relativeNormalCoordinate U z=
      HironakaActualCentreJointJets.actualJointNormalProjection n 1 z.val 0 := by
    simp [relativeNormalCoordinate,HironakaActualZeroCoordinateContactSeed.addedCoordinate,
      HironakaActualGraphFunctionalIdeal.graphFunction,HironakaActualZeroCoordinateContactSeed.zeroFunction]
  rw [hcoord]
  simp only [mem_univ,and_true]
  constructor
  · rintro ⟨hN,hz⟩
    refine ⟨hN,?_⟩
    ext i
    have hi : i=(0 : Fin 1):=Subsingleton.elim _ _
    simpa only [hi,WithLp.ofLp_zero,Pi.zero_apply] using hz
  · rintro ⟨hN,hz⟩
    exact ⟨hN,congrArg (fun v : ComplexModel 1=>v 0) hz⟩

private theorem section_projection_ideal {I : GermIdeal n U} (hI : I.IsCoherent) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (GermIdeal.pullback (m:=n+1) (projection U) I)=I := by
  have he : (projection U)∘(zeroSection U)=id := by
    funext x
    apply Subtype.ext
    exact tangentProjection_tangentInclusion n 1 x.val
  rw [←coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U) I hI,
    he,BlowupControlledTransform.pullback_id hI]

private theorem section_equal_restrictEquiv (A : Set U) (E : List (Set (productOpen U))) (d : ℕ)
    {I J : GermIdeal (n+1) (productOpen U)} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (h : GermIdeal.pullback (m:=n) (zeroSection U) I=
      GermIdeal.pullback (m:=n) (zeroSection U) J) :
    RestrictEquiv (⟨liftedCarrier A,E,I,d⟩ : MarkedIdeal (n+1) (productOpen U))
      (⟨liftedCarrier A,E,J,d⟩ : MarkedIdeal (n+1) (productOpen U)) := by
  have hA:=restrictEquiv_actual_open_section U A E d I (hol hI)
  have hB:=restrictEquiv_actual_open_section U A E d J (hol hJ)
  have hr : GermIdeal.pullback (m:=n+1) (zeroSection U∘projection U) I=
      GermIdeal.pullback (m:=n+1) (zeroSection U∘projection U) J := by
    rw [coherent_pullback_comp (zeroSection_contMDiff U) (projection_contMDiff U) I hI,
      coherent_pullback_comp (zeroSection_contMDiff U) (projection_contMDiff U) J hJ,h]
  exact ⟨rfl,rfl,rfl,
    RestrictLeCalculus.RestrictLe.trans hA.le (by rw [hr];exact hB.ge),
    RestrictLeCalculus.RestrictLe.trans hB.le (by rw [←hr];exact hA.ge)⟩

/-- Actual cylinder and section have the FULL local blowup/product/open test class. -/
theorem properNormalMarked_locWPEquiv_section (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    LocWPEquiv (X:=CMfd.of (n:=n+1) (productOpen U)) (properNormalMarked Q) (sectionMarked Q) := by
  let P:=properNormalMarked Q
  let S:=sectionMarked Q
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hS:=section_domain Q hQ
  have hCP:=isCoherent_coeffMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  have hCS:=isCoherent_coeffMarkedAlong hS.isWellFormed.isCoherent hS.isWellFormed.isClosedSubmanifold_N
  have hContact:=locWPEquiv_contact_along (X:=CMfd.of (n:=n+1) (productOpen U)) P
    hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hP.one_le_d
    (properNormalMarked_tangent Q hQ.one_le_d)
  rw [contact_carrier Q] at hContact
  have hTraceP : GermIdeal.pullback (m:=n) (zeroSection U) (coeffMarkedAlong P).ideal=
      (coeffMarkedAlong Q).ideal:=
    congrArg MarkedIdeal.ideal (markedPullback_coeffMarkedAlong Q
      hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent)
  have hTraceS : GermIdeal.pullback (m:=n) (zeroSection U) (coeffMarkedAlong S).ideal=
      (coeffMarkedAlong Q).ideal := by
    have h:=markedPullback_section_coeffMarkedAlong Q.N hQ.isWellFormed.isClosedSubmanifold_N
      Q.E (GermIdeal.pullback (m:=n+1) (projection U) Q.ideal)
      (isCoherent_pullback (projection_contMDiff U) hQ.isWellFormed.isCoherent) Q.d
    rw [section_projection_ideal hQ.isWellFormed.isCoherent] at h
    exact congrArg MarkedIdeal.ideal h
  have hRE : RestrictEquiv (withN (coeffMarkedAlong P) (liftedCarrier Q.N)) (coeffMarkedAlong S) :=
    section_equal_restrictEquiv Q.N _ _ hCP hCS (hTraceP.trans hTraceS.symm)
  have hCoeff : LocWPEquiv (X:=CMfd.of (n:=n+1) (productOpen U))
      (withN (coeffMarkedAlong P) (liftedCarrier Q.N)) (coeffMarkedAlong S) :=
    locEquiv_of_restrictEquiv_closed (κ:=Kinds.wp) rfl hRE
      hS.isWellFormed.isClosedSubmanifold_N hCP hCS
  exact hContact.trans (hCoeff.trans (coefficient_local_any_boundary (X:=CMfd.of (n:=n+1) (productOpen U)) S hS).symm)

/-- Genuine original kept lower class, no future class or canonical correspondence input. -/
theorem keptNormalLower_locWPEquiv_sectionBarCoefficient (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    LocWPEquiv (X:=CMfd.of (n:=n+1) (productOpen U)) (keptNormalLower Q) (sectionBarCoefficient Q) := by
  let P:=properNormalMarked Q
  let S:=sectionMarked Q
  let B:=barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) P
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hS:=section_domain Q hQ
  have hB:=isInvDomain_barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) P hP
  have hSB:=isInvDomain_barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) S hS
  have hContact:=locWPEquiv_contact_along (X:=CMfd.of (n:=n+1) (productOpen U)) B
    hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent hB.one_le_d (bar_normal_tangent Q hQ)
  change LocWPEquiv B (withN (coeffMarkedAlong B)
    ((properNormalMarked Q).N∩{z|relativeNormalCoordinate U z=0}∩univ)) at hContact
  rw [contact_carrier Q] at hContact
  have hPB : LocWPEquiv (X:=CMfd.of (n:=n+1) (productOpen U)) P B:=
    bar_local_any_boundary (X:=CMfd.of (n:=n+1) (productOpen U)) P hP
  have hPS : LocWPEquiv (X:=CMfd.of (n:=n+1) (productOpen U)) P S:=
    properNormalMarked_locWPEquiv_section Q hQ
  have hSBar : LocWPEquiv (X:=CMfd.of (n:=n+1) (productOpen U)) S
      (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) S):=
    bar_local_any_boundary (X:=CMfd.of (n:=n+1) (productOpen U)) S hS
  have hCoeff : LocWPEquiv (X:=CMfd.of (n:=n+1) (productOpen U))
      (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) S) (sectionBarCoefficient Q):=
    coefficient_local_any_boundary (X:=CMfd.of (n:=n+1) (productOpen U))
      (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) S) hSB
  exact hContact.symm.trans (hPB.symm.trans (hPS.trans (hSBar.trans hCoeff)))

/-- Literal same section carrier, full boundary and TRUE double coefficient mark. -/
theorem keptNormalLower_fields (Q : MarkedIdeal n U) :
    (keptNormalLower Q).N=(sectionBarCoefficient Q).N ∧
    (keptNormalLower Q).E=(sectionBarCoefficient Q).E ∧
    (keptNormalLower Q).d=(sectionBarCoefficient Q).d := ⟨rfl,rfl,rfl⟩

end
end Hironaka.HironakaG1ProperCarrierNormalLocalClass
