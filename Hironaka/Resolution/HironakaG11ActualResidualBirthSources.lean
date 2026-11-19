import Hironaka.Resolution.HironakaG11ResidualActualContact
import Hironaka.Resolution.HironakaG11ResidualSelectedOld
import Hironaka.Resolution.HironakaG11RetainedBirthContainmentOther

set_option autoImplicit false

/-! The true successor residual chooses one birth carrying both contact
configurations and the full retained-source centre-germ dictionary. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ActualResidualBirthSources
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MemberInterLocusAlong BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong
  TangentDirectionAlong ResolutionInvariantSpec HomogenizedIdealAlong StepOneValue
  HironakaG8LocalHistory HironakaG11InvBMLower HironakaG11InvBMMask
  HironakaG11InvBMLowerTailSucc HironakaG11ResidualActualContact
  HironakaG11RetainedBirthContainment HironakaG11RetainedBirthContainmentOther

/-- The residual selects a single actual born member and, regardless of
which exceptional divisibility alternative holds, every original member
through the distinct anchor has a smooth source whose germ contains the
same birth centre. -/
theorem residual_birth_has_all_retained_sources
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T)
    (a z : Y) (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp)
    (s : ℕ) (hreg : stepRegime A (s+1) T a) (O : Opens Y)
    (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a) (hzO : z ∈ O)
    {H : Set Y} (hH : H ∈ (lowerIdealBM A (s+1) T a).E)
    (hzA : z ∈ (lowerIdealBM A (s+1) T a).N)
    (hzB : z ∈ (lowerIdealBM B (s+1) T a).N) (hzH : z ∈ H)
    (hdiv : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d) H 1 z ∨
      IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d) H 1 z) :
    ∃ (Y₀ Y₁ : CMfd.{0} n) (P : BlowupTower X Y₀) (C : Set Y₀)
      (π : Y₁ → Y₀) (hπ : IsBlowupAlong n C π) (Q : BlowupTower Y₁ Y) (U : Opens X),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) ∧
      IsTangentDirectionAlong A.N A.ideal A.d U (tangentChoice A (T.proj a)).2 ∧
      IsTangentDirectionAlong B.N B.ideal B.d U (tangentChoice B (T.proj a)).2 ∧
      P.proj (π (Q.proj z)) ∈ U ∧
      (lowerIdealBM A (s+1) T a).N = strictAlong Q
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 (BlowupTower.step P C π hπ)).N ∧
      (lowerIdealBM B (s+1) T a).N = strictAlong Q
        (contactCoeffBM B (tangentChoice B (T.proj a)).2 (BlowupTower.step P C π hπ)).N ∧
      (∀ K ∈ throughMembers A T a, ∃ H₀ ∈ (geoTransformAlong A P).E,
        IsClosedSubmanifold n H₀ ∧ IsClosedSubmanifold n (geoStrictTransform π C H₀) ∧
        K = strictAlong Q (geoStrictTransform π C H₀) ∧
        ∀ᶠ x in 𝓝 (π (Q.proj z)), x ∈ C → x ∈ H₀) := by
  have hS := isClosedSubmanifold_of_mem_throughMembers A hA.isWellFormed hn T hT a
  have hSne := throughMembers_ne_nil A T hreg.1
  obtain ⟨K,hK⟩ := List.exists_mem_of_ne_nil (throughMembers A T a) hSne
  obtain ⟨Y₀,Y₁,P,C,π,hπ,Q,K₀,U,p,hEq,hH',hK₀,hK',hpEq,hpC,hP,hC,hQ,
    hzPA,hzPB,hzK,hu,hv,hgeom⟩ :=
    residual_birth_has_paired_contact hA hB hmA hmB h T hT a z ha s O hOA hOB hzO
      hH hK (fun K hK => (hS K hK).1) hzA hzB hzH hdiv
  have hpU : P.proj (π (Q.proj z)) ∈ U := by
    rw [← hpEq]
    exact p.property
  have hNA : (lowerIdealBM A (s+1) T a).N = strictAlong Q
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 (BlowupTower.step P C π hπ)).N := by
    rw [lowerIdealBM_N,hEq,strictAlong_append,contactCoeffBM_N]
  have hNB : (lowerIdealBM B (s+1) T a).N = strictAlong Q
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 (BlowupTower.step P C π hπ)).N := by
    rw [lowerIdealBM_N,hEq,strictAlong_append,contactCoeffBM_N]
  have hTest : IsGeoTestTower (barMarked A) ((BlowupTower.step P C π hπ).append Q) := hEq ▸ hT
  have hzD : z ∈ strictAlong Q (π ⁻¹' C) := hH' ▸ hzH
  have hSources : ∀ K ∈ throughMembers A T a, ∃ H₀ ∈ (geoTransformAlong A P).E,
      IsClosedSubmanifold n H₀ ∧ IsClosedSubmanifold n (geoStrictTransform π C H₀) ∧
      K = strictAlong Q (geoStrictTransform π C H₀) ∧
      ∀ᶠ x in 𝓝 (π (Q.proj z)), x ∈ C → x ∈ H₀ := by
    rcases hdiv with hdivA | hdivB
    · have hdA' : IsDivNearAlong n (strictAlong Q
          (contactCoeffBM A (tangentChoice A (T.proj a)).2 (BlowupTower.step P C π hπ)).N)
          (exceptionalTermBM (n := n) (throughMembers A ((BlowupTower.step P C π hπ).append Q) a)
            (coeffEmptyBM A).d) (strictAlong Q (π ⁻¹' C)) 1 z := by
        rw [←hNA,←hH',←hEq]
        exact hdivA
      have hs := retained_sources_contain_birth_centre_germ hn A hA U hu P C π hπ Q hTest a z
        hpU (hNA ▸ hzA) hzD hdA'
      simpa only [←hEq] using hs
    · have hdB' : IsDivNearAlong n (strictAlong Q
          (contactCoeffBM B (tangentChoice B (T.proj a)).2 (BlowupTower.step P C π hπ)).N)
          (exceptionalTermBM (n := n) (throughMembers A ((BlowupTower.step P C π hπ).append Q) a)
            (coeffEmptyBM A).d) (strictAlong Q (π ⁻¹' C)) 1 z := by
        rw [←hNB,←hH',←hEq]
        exact hdivB
      have hs := retained_sources_contain_birth_centre_germ_other hn A B hA hB h hd hE U hv
        P C π hπ Q hTest a z hpU (hNB ▸ hzB) hzD hdB'
      simpa only [←hEq] using hs
  exact ⟨Y₀,Y₁,P,C,π,hπ,Q,U,hEq,hH',hu,hv,hpU,hNA,hNB,hSources⟩

end Hironaka.HironakaG11ActualResidualBirthSources
