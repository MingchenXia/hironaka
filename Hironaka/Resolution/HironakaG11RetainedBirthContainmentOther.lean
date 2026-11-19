import Hironaka.Resolution.HironakaG11RetainedBirthContainment
import Hironaka.Resolution.HironakaG8ClassStepResidual

set_option autoImplicit false

/-! The retained-source birth containment is symmetric for the second
original contact carrier with the first record's retained member list. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11RetainedBirthContainmentOther
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong
  TangentDirectionAlong ResolutionInvariantSpec HironakaG8LocalHistory
  StepOneValue HironakaG11InvBMLower HironakaG8ClassStepResidual
  HironakaG11RetainedBirthContainment

/-- The second actual carrier yields the same smooth source-member and
centre-germ dictionary for the first record's retained exceptional list. -/
theorem retained_sources_contain_birth_centre_germ_other
    {n : ℕ} (hn : 0 < n) {X Y₀ Y₁ Y : CMfd.{0} n} (A B : MarkedIdeal n X) {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B) (h : LocWPEquiv A B)
    (hd : A.d = B.d) (hE : A.E = B.E) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong B.N B.ideal B.d U u)
    (P : BlowupTower X Y₀) (C : Set Y₀) (π : Y₁ → Y₀) (hπ : IsBlowupAlong n C π)
    (Q : BlowupTower Y₁ Y)
    (hT : IsGeoTestTower (barMarked A) ((BlowupTower.step P C π hπ).append Q))
    (a z : Y) (hzU : P.proj (π (Q.proj z)) ∈ U)
    (hzP : z ∈ strictAlong Q (contactCoeffBM B u (.step P C π hπ)).N)
    (hzD : z ∈ strictAlong Q (π ⁻¹' C))
    (hdiv : IsDivNearAlong n (strictAlong Q (contactCoeffBM B u (.step P C π hπ)).N)
      (exceptionalTermBM (n := n) (throughMembers A ((BlowupTower.step P C π hπ).append Q) a)
        (coeffEmptyBM A).d) (strictAlong Q (π ⁻¹' C)) 1 z) :
    ∀ K ∈ throughMembers A ((BlowupTower.step P C π hπ).append Q) a,
      ∃ H ∈ (geoTransformAlong A P).E, IsClosedSubmanifold n H ∧
        IsClosedSubmanifold n (geoStrictTransform π C H) ∧
        K = strictAlong Q (geoStrictTransform π C H) ∧
        ∀ᶠ x in 𝓝 (π (Q.proj z)), x ∈ C → x ∈ H := by
  let T := (BlowupTower.step P C π hπ).append Q
  have hTA : IsGeoTestTower A T := ((StepOneBridge.barMarked_wEquiv A hA).2 T).1.mp hT
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T := ((StepOneBridge.barMarked_wEquiv B hB).2 T).1.mpr hTB
  have hS : throughMembers A T a = throughMembers B T a := throughMembers_eq_of_E_eq hE T a
  have hmark : (coeffEmptyBM A).d = (coeffEmptyBM B).d := by
    rw [coeffEmptyBM_d,coeffEmptyBM_d,hd]
  have hstageE : (geoTransformAlong A P).E = (geoTransformAlong B P).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE P
  have hdivB : IsDivNearAlong n (strictAlong Q (contactCoeffBM B u (.step P C π hπ)).N)
      (exceptionalTermBM (n := n) (throughMembers B T a) (coeffEmptyBM B).d)
      (strictAlong Q (π ⁻¹' C)) 1 z := by
    rw [← hS,← hmark]
    exact hdiv
  have hresult := retained_sources_contain_birth_centre_germ hn B hB U hu P C π hπ Q hTJB a z
    hzU hzP hzD hdivB
  rw [← hS,← hstageE] at hresult
  exact hresult

end Hironaka.HironakaG11RetainedBirthContainmentOther
