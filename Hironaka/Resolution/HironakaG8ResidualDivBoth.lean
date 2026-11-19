import Hironaka.Resolution.HironakaG8ResidualActualNonzero

/-! # The successor residual when both exceptional traces divide -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualDivBoth
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMLower HironakaG11InvBMMask HironakaG11InvBMLowerTailSucc
  HironakaG8ClassStepCut HironakaG8ExceptionalDivisibility HironakaG8ResidualActualNonzero
  StepOneValue StepOneLowerDomain ResolutionInvariantSpec HomogenizedIdealAlong
open HironakaG11InvBMClass (SameCarrierDim)

/-- The actual successor residual is closed when the exceptional sum is
divisible along both contact carriers. No trace hypothesis remains. -/
theorem actual_successor_exp_eq_of_div_both
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
    (hdivA : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y)
    (hdivB : IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y) :
    divExpAlong n (lowerIdealBM A (s+1) T a).N (lowerIdealBM A (s+1) T a).ideal H y =
      divExpAlong n (lowerIdealBM B (s+1) T a).N (lowerIdealBM B (s+1) T a).ideal H y := by
  have hS : ∀ D ∈ throughMembers A T a, IsClosed D := fun D hD =>
    (isClosedSubmanifold_of_mem_throughMembers A hA.isWellFormed hn T hT a D hD).1
  have hpos : 1 ≤ (coeffEmptyBM A).d := one_le_coeffEmptyBM_d A
  have htraceA := (exceptionalTerm_divisible_below_iff_trace hS (le_refl 1) hpos y).mp hdivA
  have htraceB := (exceptionalTerm_divisible_below_iff_trace hS (le_refl 1) hpos y).mp hdivB
  have htrace : (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) := by
    have ha' : ∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H →
        ∀ D ∈ throughMembers A T a, z ∈ D := by simpa only [lowerIdealBM_N,contactCoeffBM_N] using htraceA
    have hb' : ∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H →
        ∀ D ∈ throughMembers A T a, z ∈ D := by simpa only [lowerIdealBM_N,contactCoeffBM_N] using htraceB
    exact ⟨fun _ => hb', fun _ => ha'⟩
  exact actual_successor_exp_eq_of_trace_only hn hA hB hmA hmB h hd hE hdim T hT ha s hreg O hOA hOB
    hdA hdB hyO hH hy hyH hbelow (Or.inl hdivA) htrace

end
end Hironaka.HironakaG8ResidualDivBoth
