import Hironaka.Resolution.HironakaG8ResidualActualSum
import Hironaka.Resolution.HironakaG11ActualCoefficientComparison

/-! # The actual successor residual reduces to its geometric trace -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualTraceReduction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMLower HironakaG11InvBMMask HironakaG11InvBMLowerTailSucc
  HironakaG8ClassStepCut HironakaG8ResidualActualSum HironakaG11ActualCoefficientComparison
  StepOneValue StepOneLowerDomain ResolutionInvariantSpec HomogenizedIdealAlong
  MarkedIdealOperationsAlong.MarkedIdeal
open HironakaG11InvBMClass (SameCarrierDim)

/-- The only remaining comparison in this nonzero-coefficient branch is the
geometric condition on the contact traces of the original members. -/
theorem actual_successor_exp_eq_of_trace
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) {a y : Y}
    (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp) (s : ℕ) (O : Opens Y)
    (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a) (hyO : y ∈ O)
    {H : Set Y} (hH : H ∈ (lowerIdealBM A (s+1) T a).E)
    (hy : y ∈ (lowerIdealBM A (s+1) T a).cosupp) (hyH : y ∈ H)
    (hnzA : IsNonzeroAlongAt (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal y)
    (hnzB : IsNonzeroAlongAt (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal y)
    (htrace : (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D))
    (hbelow : ¬ IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal H (lowerIdealBM A (s+1) T a).d y) :
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
  have hloc := locWPEquiv_lowerIdealBM_succ hn hA hB hmA hmB h hE T hT ha s O hOA hOB
  have hCA := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T hT a (s+1)
  have hCB := HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T hTJB a (s+1)
  have hypA : (⟨y,hyO⟩ : O) ∈ (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM A (s+1) T a)).cosupp := by
    rw [cosupp_pullback_val _ (hol_of_isCoherent hCA) O]
    exact hy
  have hypB := hloc.cosupp_eq_base ▸ hypA
  have hyB : y ∈ (lowerIdealBM B (s+1) T a).N := by
    have hmem := (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM B (s+1) T a)).cosupp_subset_N hypB
    exact hmem
  have hyA : y ∈ (lowerIdealBM A (s+1) T a).N := (lowerIdealBM A (s+1) T a).cosupp_subset_N hy
  have hyAC : y ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N := by
    simpa only [lowerIdealBM_N, contactCoeffBM_N] using hyA
  have hyBC : y ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N := by
    simpa only [lowerIdealBM_N, contactCoeffBM_N] using hyB
  have hcoeff := actual_residual_coefficient_exp_below hn hA hB hmA hmB h hd hE hdim T hT ha s O hOA hOB hyO hH hy hyH hnzA hnzB
  have hcoeff' : min (divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal H y) (coeffEmptyBM A).d =
    min (divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal H y) (coeffEmptyBM A).d := by
    simpa only [contactCoeffBM_d] using hcoeff
  exact actual_successor_exp_eq_of_coeff_and_trace hn A B hA.isWellFormed hB.isWellFormed hA.one_le_d hB.one_le_d
    hd hE T hT hTB a y s H hyH W huW hvW hyW hyAC hyBC hnzA hnzB hcoeff' htrace hbelow

end
end Hironaka.HironakaG8ResidualTraceReduction
