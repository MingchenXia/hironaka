import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.ExtSeqTransport
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3CanonicalPositiveMemberData
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneValueMasked StepOneRegime
  ResolutionInvariantSpec ResolutionInvariantSeq InvDomainMemberRestriction HomogenizedIdealAlong
noncomputable section

/-- A nonspecial positive-level canonical Step One point supplies the actual member-tail data. -/
theorem canonical_positive_level_member_data {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{u} n}
    {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM R M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (hs : ¬ IsSpecial M T y) (hpos : 0 < level M T y) :
    let j := regimeRun (stepRegime M (level M T y)) T y
    let T₀ := head T j
    let T₁ := tail T j
    let a := T₁.proj y
    let A := maskA M T₀ a
    let J := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : A → _) 
      (memberRestrict (geoTransformAlong (barMarked M) T₀)
        (membersThrough (geoTransformAlong (barMarked M) T₀).E (origMembers M T₀) a))
    ∃ h : a ∈ A, IsInvDomain k J ∧ IsCanonical J (R.inv J) (restrict A T₁) ∧
      (⟨y,h⟩ : openPreimage T₁ A) ∈ (geoTransformAlong J (restrict A T₁)).cosupp := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k + 1) R M hM hmax hn T hcan
  have hc := (Seq.StepOneBridge.isCanonical_iff (k := k + 1) R M hM hmax hn T).mp hcan
  have hd := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := k + 1)
    M R hM.isWellFormed hM.one_le_d hn hmax hM.dimLE T hb.1 hc
  have hdata := hd y hy hs
  unfold Seq.StepOneValueMasked.LowerDataL at hdata
  generalize heq : level M T y = s at hdata ⊢
  cases s with
  | zero => simp [heq] at hpos
  | succ s =>
    obtain ⟨h, hD, hC, hcos⟩ := hdata
    exact ⟨h, hD, hC, hcos⟩
end
end Hironaka.G3CanonicalPositiveMemberData
