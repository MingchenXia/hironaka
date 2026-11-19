import Hironaka.Resolution.HironakaG3UniverseHigherMemberDataGeneric
import Hironaka.Resolution.HironakaG3UniverseHigherMemberValueOpenGeneric
import Hironaka.Resolution.HironakaG3UniverseLiftedSplit
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseHigherPositiveStepValueGeneric
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneValueMasked StepOneRegime ResolutionInvariantSpec CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  HironakaG3UniverseLiftedSplit G3UniverseStepOneLevel G3UniverseStepOneSpecialActual G3UniverseOpenDiffeo
  G3UniverseMemberLowerIH G3UniverseHigherMemberDataGeneric G3UniverseHigherMemberValueOpenGeneric G3UniverseCanonicalIH InvDomainMemberRestriction HomogenizedIdealAlong
noncomputable section

/-- A nonspecial positive-level canonical Step One point has its Step One value preserved by literal lift, given the lower canonical value IH. -/
theorem stepOne_lifted_positive_level_of_IH {n r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (hIH : CanonicalLiftValueIH.{u} hn r) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (hs : ¬ IsSpecial M T y) (hpos : 0 < level M T y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
      (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) ((liftDiffeomorph.{u} Y) y) =
    Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M T y := by
  classical
  let ML := markedPullback (m := n) (liftDiffeomorph.{u} X).symm M
  let yL := (liftDiffeomorph.{u} Y) y
  let s := level M T y
  let j := regimeRun (stepRegime M s) T y
  let T₀ := head T j
  let T₁ := tail T j
  let a := T₁.proj y
  let z := (liftTower.{u} T₁).proj yL
  let A := maskA M T₀ a
  let V := maskA ML (liftTower.{u} T₀) z
  obtain ⟨hmem,hD,hC,hcos⟩ := canonical_positive_level_member_data hn M hM hmax T hcan y hy hs hpos
  have hbar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := r + 1) (invFamily.{0} hn r) M hM hmax hn T hcan).1
  have hT₀ : IsGeoTestTower (barMarked M) T₀ := ((isGeoTestTower_iff_head_tail (barMarked M) T j).mp hbar).1
  have hlevel : level ML (liftTower.{u} T) yL = s := by
    simpa only [ML,yL,s,Diffeomorph.symm_apply_apply] using level_liftTower_barTest M hM.isWellFormed T hbar yL
  have hrun : regimeRun (stepRegime ML s) (liftTower.{u} T) yL = j := by
    simpa only [ML,yL,j,Diffeomorph.symm_apply_apply] using stepRegimeRun_liftTower M hM.isWellFormed s T hbar yL
  have hsL : ¬ IsSpecial ML (liftTower.{u} T) yL := by
    intro h; apply hs
    simpa only [ML,yL,Diffeomorph.symm_apply_apply] using (isSpecial_liftTower M hM.isWellFormed T hbar yL).mp h
  have hz : z = (liftDiffeomorph.{u} (split T j).1) a := by
    dsimp only [z,yL,a]
    rw [liftTower_proj]
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
  have hV : V = preimageOpens (liftDiffeomorph.{u} (split T j).1).symm A := by
    change maskA ML (liftTower.{u} T₀) z = _
    rw [hz]
    simpa only [ML,A,a,Diffeomorph.symm_apply_apply] using
      maskA_liftTower M hM.isWellFormed T₀ hT₀ ((liftDiffeomorph.{u} (split T j).1) a)
  have hmemL : (liftTower.{u} T₁).proj yL ∈ V := by
    change z ∈ V
    rw [hV]
    change (liftDiffeomorph.{u} (split T j).1).symm z ∈ A
    rw [hz]
    simpa only [A,a,Diffeomorph.symm_apply_apply] using hmem
  have hval := member_value_lift_of_point_eq hn M hM.isWellFormed T₀ hT₀ T₁ a z hz hD hC hIH V rfl y hmem hmemL hcos
  have hLow : Seq.StepOneValueMasked.lowerValueL (invFamily.{u} hn r) ML (lowerMarkedM ML) s (liftTower.{u} T₀)
      (liftTower.{u} T₁) yL = Seq.StepOneValueMasked.lowerValueL (invFamily.{0} hn r) M (lowerMarkedM M) s T₀ T₁ y := by
    unfold Seq.StepOneValueMasked.lowerValueL
    have hspos : 0 < s := hpos
    generalize heq : s = t
    cases t with
    | zero => simp [heq] at hspos
    | succ t =>
      have hgL : (liftTower.{u} T₁).proj yL ∈ lowerMask ML (t + 1) (liftTower.{u} T₀) ((liftTower.{u} T₁).proj yL) := hmemL
      have hg : T₁.proj y ∈ lowerMask M (t + 1) T₀ (T₁.proj y) := hmem
      rw [dif_pos hgL, dif_pos hg]
      change (invFamily.{u} hn r).inv
        (lowerMarkedM ML (t + 1) (liftTower.{u} T₀) ((liftTower.{u} T₁).proj yL))
        (restrict (lowerMask ML (t + 1) (liftTower.{u} T₀) ((liftTower.{u} T₁).proj yL)) (liftTower.{u} T₁)) ⟨yL,hgL⟩ =
        (invFamily.{0} hn r).inv (lowerMarkedM M (t + 1) T₀ (T₁.proj y))
          (restrict (lowerMask M (t + 1) T₀ (T₁.proj y)) T₁) ⟨y,hg⟩ at hval
      exact congrArg WithTop.some hval
  have hLow' : Seq.StepOneValueMasked.lowerValueL (invFamily.{u} hn r) ML (lowerMarkedM ML) s
      (head (liftTower.{u} T) j) (tail (liftTower.{u} T) j) yL =
      Seq.StepOneValueMasked.lowerValueL (invFamily.{0} hn r) M (lowerMarkedM M) s T₀ T₁ y := by
    unfold head tail
    rw [liftTower_split]
    exact hLow
  change Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r) ML (liftTower.{u} T) yL =
    Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M T y
  simp only [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL, if_neg hsL, if_neg hs,
    hlevel]
  rw [← hlevel] at hrun
  rw [hrun]
  exact congrArg (fun q => toLex (s,q)) hLow'
end
end Hironaka.G3UniverseHigherPositiveStepValueGeneric
