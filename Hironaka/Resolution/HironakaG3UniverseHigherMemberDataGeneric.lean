import Hironaka.Resolution.HironakaG3CanonicalPositiveMemberData
import Hironaka.Resolution.HironakaG3UniverseMemberCanonicalIH
import Hironaka.Invariant.ExtSeqTransport
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseHigherMemberDataGeneric
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneValueMasked StepOneRegime
  ResolutionInvariantSpec CanonicalCentres HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower G3UniverseMemberLowerIH HomogenizedIdealAlong
noncomputable section

/-- The actual nonspecial positive-level canonical Step One point supplies its original member-tail data. -/
theorem canonical_positive_level_member_data {n r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (hs : ¬ IsSpecial M T y) (hpos : 0 < level M T y) :
    let j := regimeRun (stepRegime M (level M T y)) T y
    let T₀ := head T j
    let T₁ := tail T j
    let z := (liftDiffeomorph.{u} _) (T₁.proj y)
    let J := originalLowerMember M T₀ z
    ∃ h : T₁.proj y ∈ maskA M T₀ (T₁.proj y),
      IsInvDomain r J ∧ IsCanonical J ((invFamily.{0} hn r).inv J) (restrict (maskA M T₀ (T₁.proj y)) T₁) ∧
      (⟨y,h⟩ : openPreimage T₁ (maskA M T₀ (T₁.proj y))) ∈
        (geoTransformAlong J (restrict (maskA M T₀ (T₁.proj y)) T₁)).cosupp := by
  obtain ⟨h,hD,hC,hcos⟩ := G3CanonicalPositiveMemberData.canonical_positive_level_member_data
    hn (invFamily.{0} hn r) M hM hmax T hcan y hy hs hpos
  exact ⟨h,hD,hC,hcos⟩

end
end Hironaka.G3UniverseHigherMemberDataGeneric
