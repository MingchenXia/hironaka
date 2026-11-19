import Hironaka.Resolution.HironakaG8CaseTActualHistory
import Hironaka.Resolution.HironakaG11ActualPrefixedSum

set_option autoImplicit false

/-! At an actual residual endpoint, the two contact coefficient exponents
agree below their common mark, provided both coefficient germs are nonzero. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ActualCoefficientComparison
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMLower HironakaG11InvBMMask
  HironakaG11InvBMLowerTailSucc HironakaG8CaseTActualHistory HironakaG8ClassStepHistory
  StepOneValue StepOneLowerDomain ResolutionInvariantSpec HomogenizedIdealAlong
  MarkedIdealOperationsAlong.MarkedIdeal RestrictedIdealExtension
open HironakaG11InvBMClass (SameCarrierDim)

noncomputable section

/-- Comparison of the literal coefficient exponents at a successor residual
point, from original local equivalence and the true test history. -/
theorem actual_residual_coefficient_exp_below
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) {a z : Y}
    (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp) (s : ℕ) (O : Opens Y)
    (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a) (hzO : z ∈ O)
    {H : Set Y} (hH : H ∈ (lowerIdealBM A (s+1) T a).E)
    (hz : z ∈ (lowerIdealBM A (s+1) T a).cosupp) (hzH : z ∈ H)
    (hnzA : IsNonzeroAlongAt (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal z)
    (hnzB : IsNonzeroAlongAt (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal z) :
    let CA := contactCoeffBM A (tangentChoice A (T.proj a)).2 T
    let CB := contactCoeffBM B (tangentChoice B (T.proj a)).2 T
    min (divExpAlong n CA.N CA.ideal H z) CA.d = min (divExpAlong n CB.N CB.ideal H z) CA.d := by
  have hWA := StepOneBridge.barMarked_wEquiv A hA
  have hWB := StepOneBridge.barMarked_wEquiv B hB
  have hTA : IsGeoTestTower A T := (hWA.2 T).1.mp hT
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T := (hWB.2 T).1.mpr hTB
  have haA : a ∈ (geoTransformAlong A T).cosupp := (hWA.2 T).2 hT ▸ ha
  have haB : a ∈ (geoTransformAlong (barMarked B) T).cosupp := by
    rw [(hWB.2 T).2 hTJB, ← (h.wEquiv.2 T).2 hTA]
    exact haA
  obtain ⟨-, hu⟩ := tangentChoice_spec A
    (exists_tangent_of_mem_cosupp A hA.isWellFormed hA.one_le_d hmA T hT ha)
  obtain ⟨-, hv⟩ := tangentChoice_spec B
    (exists_tangent_of_mem_cosupp B hB.isWellFormed hB.one_le_d hmB T hTJB haB)
  let W : Opens X := ⟨(tangentChoice A (T.proj a)).1 ∩ (tangentChoice B (T.proj a)).1,
    hu.isOpen.inter hv.isOpen⟩
  have hzUA : T.proj z ∈ (tangentChoice A (T.proj a)).1 := by
    have hpre : z ∈ T.proj ⁻¹' (tangentChoice A (T.proj a)).1 :=
      interior_subset (show z ∈ interior (T.proj ⁻¹' (tangentChoice A (T.proj a)).1) from (hOA hzO).2)
    exact hpre
  have hzUB : T.proj z ∈ (tangentChoice B (T.proj a)).1 := by
    have hpre : z ∈ T.proj ⁻¹' (tangentChoice B (T.proj a)).1 :=
      interior_subset (show z ∈ interior (T.proj ⁻¹' (tangentChoice B (T.proj a)).1) from (hOB hzO).2)
    exact hpre
  have hzW : z ∈ openPreimage T W := ⟨hzUA,hzUB⟩
  have hC := (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hA.isWellFormed).isClosedSubmanifold_N
    (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hA.isWellFormed).isCoherent T
    (HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d T
      (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A T hTA))).2
  have hEc := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM
    (isClosedSubmanifold_of_mem_throughMembers A hA.isWellFormed hn T hT a) (coeffEmptyBM A).d
  have hzC : z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).cosupp := by
    have hz' := hz
    change z ∈ cosupport n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal (lowerIdealBM A (s+1) T a).d at hz'
    rw [lowerIdealBM_succ_ideal,lowerIdealBM_d,
      IdealOrderArithmetic.cosupport_sumIdeal (hol_of_isCoherent hC) (hol_of_isCoherent hEc)] at hz'
    have hN : (lowerIdealBM A (s+1) T a).N =
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N := by
      rw [lowerIdealBM_N,contactCoeffBM_N]
    rw [hN] at hz'
    change z ∈ cosupport n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).d
    rw [contactCoeffBM_ideal,contactCoeffBM_d]
    exact hz'.1
  have hCH : H ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).E := by
    rw [contactCoeffBM_E, ← lowerIdealBM_E A T a (s+1)]
    exact hH
  have hcomp := expAgreeBelowAt_contactCoeffBM_actual hA hB h hd hE hdim hu hv W
    (fun _ hx => hx.1) (fun _ hx => hx.2) T hTA hzW hnzA hnzB
  exact hcomp H hCH hzC hzH

end
end Hironaka.HironakaG11ActualCoefficientComparison
