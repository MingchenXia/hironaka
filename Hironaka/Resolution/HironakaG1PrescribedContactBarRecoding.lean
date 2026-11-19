import Hironaka.Resolution.HironakaG1ClassReferenceContact
import Hironaka.Resolution.HironakaG1ChosenCommonContactClassData
import Hironaka.Resolution.HironakaG1CoefficientCarrierClassData
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical

/-! The whole original bar on a fixed genuine coefficient contact. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1PrescribedContactBarRecoding

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres DivisorExponentAlong
  RelativePrincipalizationSpan GermIdealOrder
  HomogenizedIdealAlong StepOneValue TangentDirectionAlong CoefficientIdealRestriction
  HironakaG8LocalHistory HironakaG8LocalContact HironakaG8LocalContactStage HironakaG8HomStable
  HironakaCoherentTransformExtension HironakaG8ContactMax ContactIndependenceAlong
  HironakaG8GapNormalizedExponent HironakaG11InvBMClass
  HironakaActualCoefficientDivisorExponentGap HironakaG1ClassReferenceContact
  HironakaG1ChosenCommonContactClassData HironakaG1OriginalUnequalMarkCanonical
  HironakaG1CoefficientCarrierClassData

private theorem contact_coefficient_hasCosupportGap {n k : ℕ} {X : CMfd.{0} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain k K) (F : Set X) (hF : F ⊆ K.N) :
    HasCosupportGap (withN (coeffMarkedAlong K) F) := by
  intro x _hx hx
  have hGap := coefficient_restriction_cosupport_gap K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d F hF
  change x ∈ cosupport n F (coeffMarkedAlong K).ideal (coeffMarkedAlong K).d
  rw [← hGap]
  exact hx

set_option maxHeartbeats 800000 in
/-- The coefficient cut on a prescribed contact and its original
bar-derived cut have the same full weak class and normalized exponents.
The domain of the first cut gives the domain of the second. -/
theorem prescribed_contact_bar_data {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain k K)
    (u : X → ℂ) (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u) :
    let F := K.N ∩ {z | u z = 0}
    let C := withN (coeffMarkedAlong K) F
    let D := withN (coeffMarkedAlong (barMarked K)) F
    IsInvDomain l C → IsInvDomain l D ∧ LocWPEquiv C D ∧
      (∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
        D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x) := by
  intro F C D hC
  let B := barMarked K
  have hB := isInvDomain_barMarked (X := X) K hK
  have hF : F ⊆ K.N := inter_subset_left
  have hClosed : IsClosedSubmanifold n F := hC.isWellFormed.isClosedSubmanifold_N
  have hMaxContact : MaxContact K F := by
    simpa only [inter_univ] using (maxContact_base K hK.isWellFormed.isCoherent hu)
  have hKC : LocWPEquiv K C := locWPEquiv_of_reference_maxContact K K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
    rfl (LocEquiv.refl Kinds.wp K) F hClosed hF hMaxContact
  have hKB : LocWPEquiv K B := bar_local_any_boundary K hK
  have hBD : LocWPEquiv B D := locWPEquiv_of_reference_maxContact B K
    hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent hB.one_le_d
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
    rfl hKB.symm F hClosed hF hMaxContact
  have hCD : LocWPEquiv C D := hKC.symm.trans (hKB.trans hBD)
  have hDCoh : D.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hB.isWellFormed.isCoherent hB.isWellFormed.isClosedSubmanifold_N
  have hD : IsInvDomain l D := isInvDomain_of_sameCarrier_cosupp D C hC hDCoh
    (one_le_coeffMarkedAlong_d B) rfl rfl hCD.cosupp_eq_base.symm
  refine ⟨hD, hCD, ?_⟩
  exact normalized_exponents_of_gap_sameCarrierDim hn C D hC hD hCD
    (SameCarrierDim.of_N_eq rfl) (contact_coefficient_hasCosupportGap K hK F hF)
    (contact_coefficient_hasCosupportGap B hB F hF)

/-- The original recursive canonicality transfers between the two actual
records on the same prescribed contact at their respective literal marks. -/
theorem prescribed_contact_bar_canonical_iff {n k l : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain k K)
    (u : X → ℂ) (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (T : BlowupTower X Y) :
    let F := K.N ∩ {z | u z = 0}
    let C := withN (coeffMarkedAlong K) F
    let D := withN (coeffMarkedAlong (barMarked K)) F
    IsInvDomain l C →
      (IsCanonical C ((invFamily hn l).inv C) T ↔
        IsCanonical D ((invFamily hn l).inv D) T) := by
  intro F C D hC
  obtain ⟨hD, hLocal, hExp⟩ := prescribed_contact_bar_data hn K hK u hu hC
  exact invFamily_isCanonical_iff_of_local hn C D hC hD hLocal
    (SameCarrierDim.of_N_eq rfl) hExp T

end

end Hironaka.HironakaG1PrescribedContactBarRecoding
