import Hironaka.Resolution.HironakaG3UniverseCanonicalSimultaneous
import Hironaka.Resolution.HironakaG3UniverseStepOneLocalBridgeGeneral
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseStepOneSuccCanonical
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres StepOneValue
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseGenericCanonicalValues G3UniverseCanonicalSimultaneous G3UniverseStepOneLocalBridgeGeneral G3UniverseCanonicalIH HomogenizedIdealAlong
noncomputable section

/-- The established local Step One bridge yields actual canonicality of the whole literal lift. -/
theorem stepOne_succ_canonical_lift_and_values {n r : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn r) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M) T) :
    IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
        (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T) ∧
    ∀ y : Y, y ∈ (geoTransformAlong M T).cosupp →
      Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
        (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) ((liftDiffeomorph.{u} Y) y) =
      Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M T y := by
  let F₀ : ∀ {A : CMfd.{0} n}, MarkedIdeal n A → ∀ {B : CMfd.{0} n}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy r) :=
    fun {A} J {B} Q z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily.{0} hn r) J (Y := B) Q z
  let Fᵤ : ∀ {A : CMfd.{u} n}, MarkedIdeal n A → ∀ {B : CMfd.{u} n}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy r) :=
    fun {A} J {B} Q z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily.{u} hn r) J (Y := B) Q z
  have hlocal : ∀ {Z : CMfd.{0} n} (Q : BlowupTower X Z), IsGeoTestTower M Q →
      IsCanonical M (F₀ M) Q →
      IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
        (Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} Q) →
      ∀ z : liftCMfd.{u} Z, (liftDiffeomorph.{u} Z).symm z ∈ (geoTransformAlong M Q).cosupp →
        Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} Q) z =
          F₀ M Q ((liftDiffeomorph.{u} Z).symm z) := by
    intro Z Q hQ hcanQ hcanQL z hz
    obtain ⟨hbar,_,hcosEq⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := r + 1)
      (invFamily.{0} hn r) M hM hmax hn Q hcanQ
    have hbarz : (liftDiffeomorph.{u} Z).symm z ∈ (geoTransformAlong (barMarked M) Q).cosupp := by
      rw [hcosEq]
      exact hz
    have hv := stepOne_lifted_canonical_of_IH hn M hM hmax hIH Q hcanQ hcanQL
      ((liftDiffeomorph.{u} Z).symm z) hbarz
    rw [(liftDiffeomorph.{u} Z).apply_symm_apply z] at hv
    exact hv
  have hT := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := r + 1) (invFamily.{0} hn r) M hM hmax hn T hcan).2.1
  have hcanonical := (canonical_prefixes_of_local_bridge F₀ Fᵤ M hM.isWellFormed hlocal T hT hcan).2
  refine ⟨hcanonical, ?_⟩
  intro y hy
  exact hlocal T hT hcan hcanonical ((liftDiffeomorph.{u} Y) y) (by simpa using hy)
end
end Hironaka.G3UniverseStepOneSuccCanonical
