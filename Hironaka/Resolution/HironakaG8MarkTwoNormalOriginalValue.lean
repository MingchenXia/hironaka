import Hironaka.Resolution.HironakaG8MarkTwoCoefficientClass
import Hironaka.Resolution.HironakaG8MarkTwoNormalCoefficientTrace
import Hironaka.Resolution.HironakaG8InitialExactContactValue
import Hironaka.Resolution.HironakaActualNormalPaddingNativeCompanion
import Hironaka.Resolution.HironakaActualSectionInitialValues

/-! Exact original initial read of the full mark-two normal contact. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8MarkTwoNormalOriginalValue
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres StepOneRegime StepOneValue ContactStageKept TangentDirectionAlong
  HomogenizedIdealAlong CoefficientIdealRestriction GermIdealOrder
  HironakaActualNormalPaddingNativeCompanion HironakaActualWeightedNormalAmbientDerivatives
  HironakaActualWeightedNormalContact HironakaActualRelativeNormalGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaActualZeroCoordinateContactSeed
  HironakaActualWeightedNormalPadding HironakaActualSectionInitialValues
  HironakaG8InitialExactContactValue HironakaG8MarkTwoCoefficientClass
  HironakaG8MarkTwoNormalCoefficientTrace HironakaG8LocalCoeff HironakaG8LocalHistory

variable {n : ℕ} {U : Opens (ComplexModel n)}
abbrev base := CMfd.of (n := n) U
abbrev ambient := CMfd.of (n := n+1) (productOpen U)

def markTwoNormalContact (Q : MarkedIdeal n U) : MarkedIdeal (n+1) (productOpen U) :=
  withN (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong (normalMarked Q))))
    (liftedCarrier (univ : Set U))

open HironakaActualGraphFunctionalIdeal HironakaActualCentreJointJets HironakaRelativeNormalIdeal

private theorem normal_zero_set :
    {z : productOpen U | relativeNormalCoordinate U z = 0} = liftedCarrier (univ : Set U) := by
  ext z
  simp only [mem_ofPred_eq,relativeNormalCoordinate,addedCoordinate,graphFunction,zeroFunction,
    Function.comp_apply,liftedCarrier, mem_univ,true_and]
  rw [show WithLp.ofLp (0 : ComplexModel 1) 0 = 0 from rfl, sub_zero]
  change actualJointNormalProjection n 1 z.val 0 = 0 ↔
    actualJointNormalProjection n 1 z.val = 0
  constructor
  · intro hz
    ext j
    have hj := Subsingleton.elim j (0 : Fin 1)
    subst j
    exact hz
  · intro hz
    rw [hz]
    rfl


open RestrictedIdealExtension GermIdealPullbackCalculus RelativePrincipalizationSpan

/-- The raw supported contact is in the actual lower domain. Its ideal
contains the entire pullback of the base nonzero ideal. -/
theorem mark_two_normal_contact_domain (Q : MarkedIdeal n U)
    (hQ : IsInvDomain n Q) (hE : Q.E = [])
    (hN : Q.N = univ) (hMark : Q.d = 2) :
    IsInvDomain n (markTwoNormalContact Q) := by
  let J := (normalMarked Q : MarkedIdeal (n+1) ambient)
  let C := (markTwoNormalContact Q : MarkedIdeal (n+1) ambient)
  have hJ : IsInvDomain (n+1) J := normalMarked_original_domain Q hQ hN
  have hJd : J.d = 2 := hMark
  have hJE : J.E = [] := by change Q.E.map (projection U ⁻¹' ·) = []; rw [hE]; rfl
  have hRaw : J.ideal.Le C.ideal := by
    change J.ideal.Le (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong J))).ideal
    rw [mark_two_double_coefficient_record_eq (X := ambient) J hJ.isWellFormed.isCoherent rfl hJd,
      mark_two_coefficient_ideal (X := ambient) J hJ.isWellFormed.isCoherent rfl hJd]
    exact le_sumIdeal_left hJ.isWellFormed.isCoherent
  have hProj : (GermIdeal.pullback (m := n+1) (projection U) Q.ideal).Le J.ideal :=
    le_sumIdeal_left (isCoherent_pullback (projection_contMDiff U) hQ.isWellFormed.isCoherent)
  have hQ0 : (⟨univ,[],Q.ideal,Q.d⟩ : MarkedIdeal n U) = Q :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN.symm hE.symm rfl rfl
  have hSupport := section_projected_domain n (univ : Set U) Q.ideal Q.d (hQ0.symm ▸ hQ)
  have hCE : C.E = [] := hJE
  have hCd : C.d = 2 := by
    change (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong J))).d = 2
    rw [mark_two_double_coefficient_record_eq (X := ambient) J hJ.isWellFormed.isCoherent rfl hJd,
      coeffMarkedAlong_d hJ.one_le_d,hJd]
    decide
  have hCC : C.ideal.IsCoherent := by
    change (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong J))).ideal.IsCoherent
    rw [mark_two_double_coefficient_record_eq (X := ambient) J hJ.isWellFormed.isCoherent rfl hJd]
    exact isCoherent_coeffMarkedAlong hJ.isWellFormed.isCoherent hJ.isWellFormed.isClosedSubmanifold_N
  change IsInvDomain n C
  refine ⟨⟨hSupport.isWellFormed.isClosedSubmanifold_N,hCC,?_,?_⟩,hSupport.dimLE,?_,?_⟩
  · rw [hCE]
    exact hSupport.isWellFormed.isSNCDivisor
  · rw [hCE]
    exact hSupport.isWellFormed.isTransverse
  · rw [hCd]
    decide
  · intro z hz
    obtain ⟨g,hg,hNZ⟩ := hSupport.isNonzeroAlongAt z hz
    exact ⟨g,hRaw z _ (hProj z _ hg),hNZ⟩

/-- The full normal contact produces the strict Step One embedding of the
raw base value. The geometry hypotheses refer to the actual padded record
and its literal marked contact. -/
theorem mark_two_normal_original_initial_value (hn : 0 < n)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) (hE : Q.E = [])
    (hN : Q.N = univ) (hMark : Q.d = 2)
    (x : U) (hx : x ∈ Q.cosupp)
    (hMax : IsMaximalOrderAlong (normalMarked Q).N (normalMarked Q).ideal (normalMarked Q).d)
    (hCos : zeroSection U x ∈ (normalMarked Q).cosupp)
    (hSpecial : ¬ IsSpecial (X := ambient) (normalMarked Q) .refl (zeroSection U x)) :
    (canonicalInvariant (n+1)).inv (X := ambient) (normalMarked Q) .refl (zeroSection U x) =
      initialContactValue n 2 ((canonicalInvariant n).inv (X := base) Q .refl x) := by
  let J := (normalMarked Q : MarkedIdeal (n+1) ambient)
  let C := (markTwoNormalContact Q : MarkedIdeal (n+1) ambient)
  let O : Opens (productOpen U) := ⊤
  let R := invFamily (Nat.succ_pos n) n
  have hC : IsInvDomain n C := mark_two_normal_contact_domain Q hQ hE hN hMark
  have hJ : IsInvDomain (n+1) J := normalMarked_original_domain Q hQ hN
  have hJE : J.E = [] := by change Q.E.map (projection U ⁻¹' ·) = []; rw [hE]; rfl
  have hJd : J.d = 2 := hMark
  have hT : IsTangentDirectionAlong J.N J.ideal J.d univ (relativeNormalCoordinate U) :=
    normal_padding_contact hQ.isWellFormed.isCoherent (lt_of_lt_of_le Nat.zero_lt_one hQ.one_le_d)
  have hRestrict : contactMarkedKept (X := ambient) J (relativeNormalCoordinate U) (.refl : BlowupTower ambient ambient) O =
      MarkedIdeal.pullback (Subtype.val : O → productOpen U) C := by
    unfold contactMarkedKept
    rw [geoTransformAlong_refl]
    change MarkedIdeal.pullback _ (withN _ ((univ : Set (productOpen U)) ∩ _)) = _
    rw [univ_inter, normal_zero_set]
    rfl
  have hLower : IsInvDomain n (contactMarkedKept (X := ambient) J (relativeNormalCoordinate U) (.refl : BlowupTower ambient ambient) O) := by
    rw [hRestrict]
    exact InvDomainTowerAlong.isInvDomain_pullback_val O hC
  let L := coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong Q))
  have hTrace : GermIdeal.pullback (m := n) (zeroSection U) C.ideal = L.ideal := by
    let Q0 : MarkedIdeal n U := ⟨univ,[],Q.ideal,2⟩
    have hQ0 : Q = Q0 := MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE rfl hMark
    have hPad : (normalPaddingIdeal Q.ideal 2).IsCoherent := by
      have h := hJ.isWellFormed.isCoherent
      change (normalPaddingIdeal Q.ideal Q.d).IsCoherent at h
      rwa [hMark] at h
    have h := mark_two_normal_double_coefficient_trace hQ.isWellFormed.isCoherent hPad
    have hJ0 : J = (⟨univ,[],normalPaddingIdeal Q.ideal 2,2⟩ :
        MarkedIdeal (n+1) (productOpen U)) := by
      refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl hJE ?_ hJd
      change normalPaddingIdeal Q.ideal Q.d = _
      rw [hMark]
    change GermIdeal.pullback (m := n) (zeroSection U)
      (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong J))).ideal =
      (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong Q))).ideal
    rw [hJ0,hQ0]
    exact h
  have hLmark : L.d = 2 := by
    change (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong Q))).d = 2
    rw [mark_two_double_coefficient_record_eq (X := base) Q hQ.isWellFormed.isCoherent hN hMark,
      coeffMarkedAlong_d hQ.one_le_d,hMark]
    decide
  have hL : (⟨univ,[],GermIdeal.pullback (m := n) (zeroSection U) C.ideal,2⟩ :
      MarkedIdeal n U) = L := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN.symm hE.symm hTrace hLmark.symm
  have hCd : C.d = 2 := by
    change (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong J))).d = 2
    rw [mark_two_double_coefficient_record_eq (X := ambient) J hJ.isWellFormed.isCoherent rfl hJd,
      coeffMarkedAlong_d hJ.one_le_d,hJd]
    decide
  have hxL : x ∈ L.cosupp := by
    change x ∈ (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong Q))).cosupp
    rw [mark_two_double_coefficient_record_eq (X := base) Q hQ.isWellFormed.isCoherent hN hMark,
      ← (locWPEquiv_coeffMarkedAlong_of_nil (X := base) Q hQ hE).cosupp_eq_base]
    exact hx
  have hxProjected : x ∈ cosupport n univ (GermIdeal.pullback (m := n) (zeroSection U) C.ideal) 2 := by
    change x ∈ (⟨univ,[],GermIdeal.pullback (m := n) (zeroSection U) C.ideal,2⟩ :
      MarkedIdeal n U).cosupp
    rwa [hL]
  have hCE : C.E = [] := hJE
  have hCeq : C = (⟨liftedCarrier (univ : Set U),[],C.ideal,2⟩ : MarkedIdeal (n+1) (productOpen U)) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl hCE rfl hCd
  have hxC : zeroSection U x ∈ C.cosupp := by
    rw [hCeq]
    change zeroSection U x ∈ cosupport (n+1) (liftedCarrier univ) C.ideal 2
    rw [source_cosupport_eq_lifted univ C.ideal
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hC.isWellFormed.isCoherent hg)]
    refine ⟨?_,?_⟩
    · have hProj : projection U (zeroSection U x) = x := by
        apply Subtype.ext
        exact tangentProjection_tangentInclusion n 1 x.val
      rwa [hProj]
    · ext j
      exact tangentInclusion_normal n 1 x.val j
  have hRead := actual_initial_family_values n hn (univ : Set U) C.ideal 2
    (hCeq ▸ hC) x hxProjected
  have hBase : (invFamily hn n).inv (X := base) L .refl x =
      (canonicalInvariant n).inv (X := base) Q .refl x := by
    have he : invFamily hn n = canonicalInvariant n := by
      cases n with
      | zero => omega
      | succ m => rfl
    rw [he]
    exact mark_two_double_coefficient_original_initial_value (X := base) Q hQ hN hE hMark x hx
  have hValue := original_initial_value_of_fixed_contact (X := ambient) (n := n) J hJ hJE hMax (zeroSection U x)
    hCos hSpecial (relativeNormalCoordinate U) univ O hT (subset_univ _) (mem_univ _) hLower
  rw [hRestrict] at hValue
  have hOpen := R.isInvValue.restrictOpen (X := ambient) C hC O (.refl : BlowupTower ambient ambient) trivial
    ⟨zeroSection U x,mem_univ _⟩ hxC
  rw [hJd] at hValue
  rw [hValue]
  apply congrArg (initialContactValue n 2)
  change R.inv (X := CMfd.of (n := n+1) O) (MarkedIdeal.pullback (Subtype.val : O → productOpen U) C) .refl
      ⟨zeroSection U x,mem_univ _⟩ = (canonicalInvariant n).inv (X := base) Q .refl x
  change R.inv (X := CMfd.of (n := n+1) O) (MarkedIdeal.pullback (Subtype.val : O → productOpen U) C) .refl
      ⟨zeroSection U x,mem_univ _⟩ = R.inv (X := ambient) C .refl (zeroSection U x) at hOpen
  rw [hOpen]
  exact (by simpa only [← hCeq,hL] using hRead : R.inv (X := ambient) C .refl (zeroSection U x) =
    (invFamily hn n).inv (X := base) L .refl x).trans hBase

end
end Hironaka.HironakaG8MarkTwoNormalOriginalValue
