import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.ContactStageKept
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3CanonicalZeroContactData
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneValueMasked StepOneRegime
  ResolutionInvariantSpec HomogenizedIdealAlong ContactStageKept
noncomputable section

/-- A nonspecial zero-level canonical Step One point supplies its actual chosen contact-tail data. -/
theorem canonical_zero_level_contact_data {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{u} n}
    {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM R M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (hs : ¬ IsSpecial M T y) (hzero : level M T y = 0) :
    let j := regimeRun (stepRegime M (level M T y)) T y
    let T₀ := head T j
    let T₁ := tail T j
    let a := T₁.proj y
    let W := maskB M T₀ a
    let w := (tangentChoice M (T₀.proj a)).2
    let J := contactMarkedKept M w T₀ W
    ∃ h : a ∈ W, IsInvDomain k J ∧ IsCanonical J (R.inv J) (restrict W T₁) ∧
      (⟨y,h⟩ : openPreimage T₁ W) ∈ (geoTransformAlong J (restrict W T₁)).cosupp := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k + 1) R M hM hmax hn T hcan
  have hc := (Seq.StepOneBridge.isCanonical_iff (k := k + 1) R M hM hmax hn T).mp hcan
  have hd := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := k + 1)
    M R hM.isWellFormed hM.one_le_d hn hmax hM.dimLE T hb.1 hc
  have hdata := hd y hy hs
  unfold Seq.StepOneValueMasked.LowerDataL at hdata
  generalize heq : level M T y = s at hdata ⊢
  cases s with
  | zero =>
    obtain ⟨h,hD,hC,hcos⟩ := hdata
    exact ⟨h,hD,hC,hcos⟩
  | succ s => simp [heq] at hzero
end
end Hironaka.G3CanonicalZeroContactData
