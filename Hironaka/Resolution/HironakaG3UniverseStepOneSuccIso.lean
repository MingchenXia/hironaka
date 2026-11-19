import Hironaka.Resolution.HironakaG3UniverseStepOneSuccCanonical
import Hironaka.Invariant.StepOneSeq
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseStepOneSuccIso
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres StepOneValue
  HomogenizedIdealAlong GermIdealOrder HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory HironakaG3UniverseMarkedDomain
  G3UniverseMarkedCosupport G3UniverseStepOneSuccCanonical G3UniverseCanonicalIH
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section

/-- An actual same-universe tower isomorphism after literal lift preserves the Step One at the supplied lower depth value. -/
theorem stepOne_succ_lift_then_iso {n r : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn r) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M) T)
    {X' Y' : CMfd.{u} n} (β : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} X)
    (Q : BlowupTower X' Y') (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y)
    (hiso : IsTowerIso β Q (liftTower.{u} T) χ) (p : Y')
    (hp : (liftDiffeomorph.{u} Y).symm (χ p) ∈ (geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
      (markedPullback (m := n) β (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) Q p =
    Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M T ((liftDiffeomorph.{u} Y).symm (χ p)) := by
  let ML := markedPullback (m := n) (liftDiffeomorph.{u} X).symm M
  have hdom : IsInvDomain (r + 1) ML := transported_markedPullback_domain X (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M hM
  have hmaxL : IsMaximalOrderAlong ML.N ML.ideal ML.d := by
    intro z hz
    let MP : MarkedIdeal n X := ⟨M.N,M.E,M.ideal,M.d+1⟩
    have hc := markedPullback_cosupp_diffeo (liftDiffeomorph.{u} X).symm MP hM.isWellFormed.isCoherent
    change cosupport n ML.N ML.ideal (ML.d+1) = (liftDiffeomorph.{u} X).symm ⁻¹' cosupport n M.N M.ideal (M.d+1) at hc
    rw [hc] at hz
    exact hmax _ hz
  obtain ⟨hbar,hT,hcosEq⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := r + 1) (invFamily.{0} hn r) M hM hmax hn T hcan
  have hresult := stepOne_succ_canonical_lift_and_values hn hIH M hM hmax T hcan
  have hcanL := hresult.1
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed T hT
  have hcos : (geoTransformAlong ML (liftTower.{u} T)).cosupp =
      (liftDiffeomorph.{u} Y).symm ⁻¹' (geoTransformAlong M T).cosupp := by
    rw [liftTower_geoTransformAlong M hM.isWellFormed T hT,
      markedPullback_cosupp_diffeo (liftDiffeomorph.{u} Y).symm _ hwf.isCoherent]
  have hpL : χ p ∈ (geoTransformAlong ML (liftTower.{u} T)).cosupp := by rw [hcos]; exact hp
  have hv := (StepOneSeq.isMaxOrderValue_stepOneInvM (k := r + 1) (invFamily.{u} hn r) hn).towerIso
    β ML hdom hmaxL Q (liftTower.{u} T) χ hiso hcanL p hpL
  have hval := hresult.2 ((liftDiffeomorph.{u} Y).symm (χ p)) hp
  rw [(liftDiffeomorph.{u} Y).apply_symm_apply (χ p)] at hval
  exact hv.trans hval
end
end Hironaka.G3UniverseStepOneSuccIso
