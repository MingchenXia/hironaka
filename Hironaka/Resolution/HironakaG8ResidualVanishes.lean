import Hironaka.Resolution.HironakaG8ResidualActualNonzero
import Hironaka.Resolution.HironakaG11ActualContactVanishing
import Hironaka.Resolution.HironakaG8ResidualTraceReduction
import Hironaka.Resolution.HironakaG11ResidualCoefficientNonzero
import Hironaka.Resolution.HironakaG8ExceptionalDivisibility

/-! # Actual nonzero coefficients from the successor residual trace -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualVanishes
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMLower HironakaG11InvBMMask HironakaG11InvBMLowerTailSucc
  HironakaG8ClassStepCut HironakaG8ClassStepExp HironakaG8SpecialLoci HironakaG8ExceptionalDivisibility
  HironakaG11ResidualCoefficientNonzero HironakaG8ResidualActualNonzero StepOneValue StepOneLowerDomain ResolutionInvariantSpec HomogenizedIdealAlong
  MarkedIdealOperationsAlong.MarkedIdeal
open HironakaG11InvBMClass (SameCarrierDim)


/-- The actual successor residual is closed when either contact coefficient vanishes along its carrier. -/
theorem actual_successor_exp_eq_of_coeff_vanishes
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) {a y : Y}
    (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp) (s : ℕ) (hreg : stepRegime A (s+1) T a)
    (O : Opens Y) (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a) {r r' : ℕ}
    (hdA : IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM A (s+1) T a)))
    (hdB : IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM B (s+1) T a)))
    (hyO : y ∈ O) {H : Set Y} (hH : H ∈ (lowerIdealBM A (s+1) T a).E)
    (hy : y ∈ (lowerIdealBM A (s+1) T a).cosupp) (hyH : y ∈ H)
    (hbelow : ¬ IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal H (lowerIdealBM A (s+1) T a).d y)
    (hdiv : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y ∨
      IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y)
    (hzero : ¬ IsNonzeroAlongAt (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal y ∨
      ¬ IsNonzeroAlongAt (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
        (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal y) :
    divExpAlong n (lowerIdealBM A (s+1) T a).N (lowerIdealBM A (s+1) T a).ideal H y =
      divExpAlong n (lowerIdealBM B (s+1) T a).N (lowerIdealBM B (s+1) T a).ideal H y := by
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
  have huW := HironakaG8LocalContact.IsTangentDirectionAlong.mono_open hu W.isOpen (fun _ hx => hx.1)
  have hvW := HironakaG8LocalContact.IsTangentDirectionAlong.mono_open hv W.isOpen (fun _ hx => hx.2)
  have hyUA : T.proj y ∈ (tangentChoice A (T.proj a)).1 := by
    have hpre : y ∈ T.proj ⁻¹' (tangentChoice A (T.proj a)).1 :=
      interior_subset (show y ∈ interior (T.proj ⁻¹' (tangentChoice A (T.proj a)).1) from (hOA hyO).2)
    exact hpre
  have hyUB : T.proj y ∈ (tangentChoice B (T.proj a)).1 := by
    have hpre : y ∈ T.proj ⁻¹' (tangentChoice B (T.proj a)).1 :=
      interior_subset (show y ∈ interior (T.proj ⁻¹' (tangentChoice B (T.proj a)).1) from (hOB hyO).2)
    exact hpre
  have hyW : y ∈ openPreimage T W := ⟨hyUA,hyUB⟩
  have hC := (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hA.isWellFormed).isClosedSubmanifold_N
    (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hA.isWellFormed).isCoherent T
    (HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d T
      (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A T hTA))).2
  have hEc := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM
    (isClosedSubmanifold_of_mem_throughMembers A hA.isWellFormed hn T hT a) (coeffEmptyBM A).d
  have hyC : y ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).cosupp := by
    have hy' := hy
    change y ∈ cosupport n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal (lowerIdealBM A (s+1) T a).d at hy'
    rw [lowerIdealBM_succ_ideal,lowerIdealBM_d,
      IdealOrderArithmetic.cosupport_sumIdeal (hol_of_isCoherent hC) (hol_of_isCoherent hEc)] at hy'
    have hN : (lowerIdealBM A (s+1) T a).N =
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N := by
      rw [lowerIdealBM_N,contactCoeffBM_N]
    rw [hN] at hy'
    change y ∈ cosupport n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).d
    rw [contactCoeffBM_ideal,contactCoeffBM_d]
    exact hy'.1
  have hcar := HironakaG11ActualContactVanishing.actual_contact_carriers_equal_of_vanishes
    A B hA.isWellFormed hB.isWellFormed hA.one_le_d hB.one_le_d h hdim W huW hvW T hTA hyW hyC hzero
  have htrace : (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) := by
    constructor
    · intro ht
      filter_upwards [ht,hcar] with z hz hc hzB hzH
      exact hz (hc.mpr hzB) hzH
    · intro ht
      filter_upwards [ht,hcar] with z hz hc hzA hzH
      exact hz (hc.mp hzA) hzH
  exact actual_successor_exp_eq_of_trace_only hn hA hB hmA hmB h hd hE hdim T hT ha s hreg O hOA hOB
    hdA hdB hyO hH hy hyH hbelow hdiv htrace

end
end Hironaka.HironakaG8ResidualVanishes
