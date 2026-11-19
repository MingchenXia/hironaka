import Hironaka.Resolution.HironakaG11ActualResidualBirthSources
import Hironaka.Resolution.HironakaG8ActualFixedBirthTrace
import Hironaka.Resolution.HironakaG8SpecialLoci

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ActualPositiveMixedTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower MemberInterLocusAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism NormalCrossings GermIdealOrder
  DivisorExponentAlong TangentDirectionAlong ResolutionInvariantSpec HomogenizedIdealAlong StepOneValue
  HironakaG8LocalHistory HironakaG8SpecialLoci HironakaG8SuccExponents HironakaG11InvBMClass HironakaG11InvBMLower
  HironakaG11InvBMMask HironakaG11InvBMLowerTailSucc HironakaG11ActualResidualBirthSources HironakaG8ActualFixedBirthTrace

/-- The actual residual trace conditions agree in the positive coefficient
branch, independently of which carrier has exceptional divisibility. -/
theorem actual_positive_mixed_trace_iff
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) {a y : Y}
    (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp) (s : ℕ) (hreg : stepRegime A (s+1) T a)
    (O : Opens Y) (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a)
    (hyO : y ∈ O) {H : Set Y} (hH : H ∈ (lowerIdealBM A (s+1) T a).E)
    (hyA : y ∈ (lowerIdealBM A (s+1) T a).N)
    (hyB : y ∈ (lowerIdealBM B (s+1) T a).N) (hyH : y ∈ H)
    (hdiv : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y ∨
      IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y)
    (hnzA : IsNonzeroAlongAt (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal y)
    (hnzB : IsNonzeroAlongAt (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal y)
    (hposA : 0 < divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal H y)
    (hposB : 0 < divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal H y) :
    (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) ↔
    (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) := by
  obtain ⟨Y₀,Y₁,P,C,π,hπ,Q,U,hEq,hH',hf,hg,hU,hNA,hNB,hsource⟩ :=
    residual_birth_has_all_retained_sources hn hA hB hmA hmB h hd hE T hT a y ha s hreg O hOA hOB hyO hH hyA hyB hyH hdiv
  have hS := isClosedSubmanifold_of_mem_throughMembers A hA.isWellFormed hn T hT a
  have hTA : IsGeoTestTower A T := ((StepOneBridge.barMarked_wEquiv A hA).2 _).1.mp hT
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 _).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T := ((StepOneBridge.barMarked_wEquiv B hB).2 _).1.mpr hTB
  have hdim' := SameCarrierDim.symm_of_cosupp_eq h.cosupp_eq_base hdim
  have hdirect : ∀ {N : Set Y}, IsDivNearAlong n N (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y →
      ∀ᶠ z in 𝓝 y, z ∈ N → z ∈ H → ∀ D ∈ throughMembers A T a, z ∈ D := by
    intro N hdv
    filter_upwards [hdv] with z hz hzN hzH D hD
    exact mem_of_mem_cosupport_one_exceptionalTermBM (fun K hK => (hS K hK).1) (hz hzN hzH) D hD
  rcases hdiv with hdivA | hdivB
  · have htA := hdirect hdivA
    have htB := actual_fixed_birth_positive_trace_transfer hn hA hB h hd hdim U hf hg P C π hπ Q
      (hEq ▸ hT) hS hU (by rw [←hEq]; simpa only [lowerIdealBM_N,contactCoeffBM_N] using hyA)
      (by rw [←hEq]; simpa only [lowerIdealBM_N,contactCoeffBM_N] using hyB) (hEq ▸ hnzA) (hEq ▸ hnzB) (hH' ▸ hyH)
      (by simpa only [←hEq, ←hH'] using hposA) (by simpa only [←hNA, ←hH'] using hdivA)
      (by intro K hK; obtain ⟨H₀,_,h1,h2,h3,h4⟩ := hsource K hK; exact ⟨H₀,h1,h2,h3,h4⟩)
    have htA' : ∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H → ∀ D ∈ throughMembers A T a, z ∈ D := by
      simpa only [←hNA,lowerIdealBM_N,contactCoeffBM_N] using htA
    have htB' : ∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H → ∀ D ∈ throughMembers A T a, z ∈ D := by
      simpa only [hH',hEq,contactCoeffBM_N,strictAlong_append] using htB
    exact ⟨fun _ => htB', fun _ => htA'⟩
  · have htB := hdirect hdivB
    have htA := actual_fixed_birth_positive_trace_transfer hn hB hA h.symm hd.symm hdim' U hg hf P C π hπ Q
      (hEq ▸ hTJB) hS hU (by rw [←hEq]; simpa only [lowerIdealBM_N,contactCoeffBM_N] using hyB)
      (by rw [←hEq]; simpa only [lowerIdealBM_N,contactCoeffBM_N] using hyA) (hEq ▸ hnzB) (hEq ▸ hnzA) (hH' ▸ hyH)
      (by simpa only [←hEq, ←hH'] using hposB) (by simpa only [←hNB, ←hH'] using hdivB)
      (by intro K hK; obtain ⟨H₀,_,h1,h2,h3,h4⟩ := hsource K hK; exact ⟨H₀,h1,h2,h3,h4⟩)
    have htB' : ∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H → ∀ D ∈ throughMembers A T a, z ∈ D := by
      simpa only [←hNB,lowerIdealBM_N,contactCoeffBM_N] using htB
    have htA' : ∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H → ∀ D ∈ throughMembers A T a, z ∈ D := by
      simpa only [hH',hEq,contactCoeffBM_N,strictAlong_append] using htA
    exact ⟨fun _ => htB', fun _ => htA'⟩
end
end Hironaka.HironakaG11ActualPositiveMixedTrace
