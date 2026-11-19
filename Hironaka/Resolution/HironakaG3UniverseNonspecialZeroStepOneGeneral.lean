import Hironaka.Resolution.HironakaG3CanonicalZeroContactChoice
import Hironaka.Resolution.HironakaG3UniverseContactChoiceGeometry
import Hironaka.Resolution.HironakaG3UniverseContactCanonicalIH
import Hironaka.Resolution.HironakaG3UniverseTangentDirection
import Hironaka.Resolution.HironakaG3UniverseStepOneSpecialActual
import Hironaka.Resolution.HironakaG3UniverseLiftedSplit
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseNonspecialZeroStepOneGeneral
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneValueMasked StepOneRegime
  StepOneLowerDomain StepOneCompare ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong GermIdealOrder
  ContactStageKept TangentDirectionAlong DerivativeIdealAlongEtale
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold HironakaG3UniverseMarkedDomain
  G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory HironakaG3UniverseLiftedSplit
  G3UniverseOpenDiffeo G3UniverseLiftRestrict G3UniverseStepOneLevel G3UniverseStepOneSpecial
  G3UniverseStepOneSpecialActual G3UniverseBarMarked G3UniverseMarkedCosupport
  G3UniverseTangentDirection G3UniverseContactChoiceGeometry G3UniverseContactLowerIH G3UniverseCanonicalIH
  G3CanonicalZeroContactData G3CanonicalZeroContactChoice
noncomputable section

/-- At a nonspecial zero-level point, the actual Step One values for a supplied lower-depth canonical lift IH agree under a canonical lift. -/
theorem stepOne_lifted_nonspecial_zero_of_IH {n r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (hIH : CanonicalLiftValueIH.{u} hn r) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M) T)
    (hcanL : IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
        (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T))
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (hs : ¬ IsSpecial M T y) (hzero : level M T y = 0) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
      (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) ((liftDiffeomorph.{u} Y) y) =
      Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M T y := by
  classical
  let eX := (liftDiffeomorph.{u} X).symm
  let ML := markedPullback (m := n) eX M
  let yL := (liftDiffeomorph.{u} Y) y
  let j := regimeRun (stepRegime M (level M T y)) T y
  let T₀ := head T j
  let T₁ := tail T j
  let a := T₁.proj y
  let W := maskB M T₀ a
  let w := (tangentChoice M (T₀.proj a)).2
  let W' := preimageOpens (liftDiffeomorph.{u} (split T j).1).symm W
  have hML : IsInvDomain (r + 1) ML := transported_markedPullback_domain X (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M hM
  have hmaxL : IsMaximalOrderAlong ML.N ML.ideal ML.d := by
    intro z hz
    let MP : MarkedIdeal n X := ⟨M.N,M.E,M.ideal,M.d+1⟩
    have hc := markedPullback_cosupp_diffeo eX MP hM.isWellFormed.isCoherent
    change cosupport n ML.N ML.ideal (ML.d+1) = eX ⁻¹' cosupport n M.N M.ideal (M.d+1) at hc
    rw [hc] at hz
    exact hmax (eX z) hz
  have hT := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := r + 1) (invFamily.{0} hn r) M hM hmax hn T hcan).1
  have hT₀ : IsGeoTestTower (barMarked M) T₀ := ((isGeoTestTower_iff_head_tail (barMarked M) T j).mp hT).1
  have hdata := canonical_zero_level_contact_data hn (invFamily.{0} hn r) M hM hmax T hcan y hy hs hzero
  obtain ⟨hmem,hdom,hcanon,hcos⟩ := hdata
  have hbar := coeffHomMarked_pullback_diffeo eX M hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N
  have hhistory := bar_history_of_base M hM.isWellFormed T hT hbar
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked M hM.isWellFormed) T hT
  have hyL : yL ∈ (geoTransformAlong (barMarked ML) (liftTower.{u} T)).cosupp := by
    rw [hhistory, markedPullback_cosupp_diffeo (liftDiffeomorph.{u} Y).symm _ hwf.isCoherent]
    simpa [yL] using hy
  have hsL : ¬ IsSpecial ML (liftTower.{u} T) yL := by
    intro h
    apply hs
    simpa [yL] using (isSpecial_liftTower M hM.isWellFormed T hT yL).mp h
  have hlevelL : level ML (liftTower.{u} T) yL = level M T y := by
    rw [level_liftTower_barTest M hM.isWellFormed T hT]
    simp [yL]
  have hzeroL : level ML (liftTower.{u} T) yL = 0 := hlevelL.trans hzero
  have hrun : regimeRun (stepRegime ML (level ML (liftTower.{u} T) yL)) (liftTower.{u} T) yL = j := by
    rw [hlevelL]
    simpa [j,yL] using stepRegimeRun_liftTower M hM.isWellFormed (level M T y) T hT yL
  have hmembers := origMembers_liftTower_barTest M hM.isWellFormed T₀ hT₀
  have hgeom := lifted_original_maskB_geometry M T₀ a hmembers
  have hx : T₀.proj a ∈ (tangentChoice M (T₀.proj a)).1 := (interior_subset hmem).1
  have hw : IsTangentDirectionAlong M.N M.ideal M.d (tangentChoice M (T₀.proj a)).1 w :=
    tangentChoice_spec_of_mem M hx
  have hloc : ∀ z : liftCMfd.{u} X, ∃ ψ : X → liftCMfd.{u} X, IsLocalInverseAt n eX ψ z := by
    intro z
    exact ⟨eX.symm, isLocalInverseAt_of_inverse
      (fun p => (eX.contMDiff p).mdifferentiableAt (by simp))
      (fun p => (eX.symm.contMDiff p).mdifferentiableAt (by simp))
      eX.apply_symm_apply eX.symm_apply_apply z⟩
  have hwL := isTangentDirectionAlong_pullback hloc
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) hw
  have hmemL : (liftTower.{u} T₁).proj yL ∈ W' := by
    change (liftDiffeomorph.{u} _).symm ((liftTower.{u} T₁).proj yL) ∈ W
    rw [liftTower_proj]
    simpa [yL,a] using hmem
  have htrans := contact_lower_canonical_and_values_of_canonical_IH hn M hM.isWellFormed T₀ hT₀ T₁ w W hdom hcanon hIH
  let p : openPreimage (liftTower.{u} T₁) W' := ⟨yL,hmemL⟩
  have hp : (liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ W p) = (⟨y,hmem⟩ : openPreimage T₁ W) := by
    apply Subtype.ext
    rfl
  have htransVal := htrans.2.2 p (by rw [hp]; exact hcos)
  rw [hp] at htransVal
  have hchoose := canonical_zero_contact_choice_values hn (invFamily.{u} hn r) ML hML hmaxL
    (liftTower.{u} T) hcanL yL hyL hsL hzeroL
  dsimp only at hchoose
  rw [hrun] at hchoose
  unfold head tail at hchoose
  rw [liftTower_split] at hchoose
  have hcomp := hchoose (w ∘ eX) (eX ⁻¹' (tangentChoice M (T₀.proj a)).1) W'
    hwL hgeom.1 hgeom.2 htrans.1 htrans.2.1 hmemL
  obtain ⟨hchosen,hchosenVal⟩ := hcomp
  have hvals := hchosenVal.trans htransVal
  have hrun0 : regimeRun (stepRegime ML 0) (liftTower.{u} T) yL = j := by
    simpa only [hzeroL] using hrun
  have hrunOrig0 : regimeRun (stepRegime M 0) T y = j := by
    simp only [j,hzero]
  have hLow : Seq.StepOneValueMasked.lowerValueL (invFamily.{u} hn r) ML (lowerMarkedM ML) 0
      (liftTower.{u} T₀) (liftTower.{u} T₁) yL =
      Seq.StepOneValueMasked.lowerValueL (invFamily.{0} hn r) M (lowerMarkedM M) 0 T₀ T₁ y := by
    unfold Seq.StepOneValueMasked.lowerValueL
    have hcL : (liftTower.{u} T₁).proj yL ∈ lowerMask ML 0 (liftTower.{u} T₀) ((liftTower.{u} T₁).proj yL) := hchosen
    have hc : T₁.proj y ∈ lowerMask M 0 T₀ (T₁.proj y) := hmem
    rw [dif_pos hcL, dif_pos hc]
    exact congrArg WithTop.some hvals
  have hLow' : Seq.StepOneValueMasked.lowerValueL (invFamily.{u} hn r) ML (lowerMarkedM ML) 0
      (head (liftTower.{u} T) j) (tail (liftTower.{u} T) j) yL =
      Seq.StepOneValueMasked.lowerValueL (invFamily.{0} hn r) M (lowerMarkedM M) 0 T₀ T₁ y := by
    unfold head tail
    rw [liftTower_split]
    exact hLow
  change Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r) ML (liftTower.{u} T) yL =
    Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M T y
  simp only [Seq.StepOneValueMasked.stepOneInvM,Seq.StepOneValueMasked.stepOneInvL,if_neg hsL,if_neg hs]
  rw [hzeroL,hzero,hrun0,hrunOrig0]
  exact congrArg (fun t => toLex (0, t)) hLow'

end
end Hironaka.G3UniverseNonspecialZeroStepOneGeneral
