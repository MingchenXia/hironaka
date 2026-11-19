import Hironaka.Resolution.HironakaG3UniverseHomCoeff
import Hironaka.Resolution.HironakaG3UniverseStepOneSpecial
import Hironaka.Resolution.HironakaG3UniverseOpenDiffeo
import Hironaka.Resolution.HironakaG3UniverseLiftedTestHistory
import Hironaka.Invariant.CanonicalCentres
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseStepOneSpecialActual
open Set Function TopologicalSpace Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseBarMarked G3UniverseStepOneSpecial G3UniverseStepOneLevel
open scoped Topology Manifold ContDiff
noncomputable section

/-- The actual Step One special locus is preserved by the literal lift. -/
theorem isSpecial_liftTower {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (y : liftCMfd.{u} Y) :
    IsSpecial (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y ↔
      IsSpecial M T ((liftDiffeomorph.{u} Y).symm y) := by
  have hb := coeffHomMarked_pullback_diffeo (liftDiffeomorph.{u} X).symm M hM.isCoherent hM.isClosedSubmanifold_N
  exact isSpecial_liftTower_of_bar_history M hM T hT (bar_history_of_base M hM T hT hb) y

/-- At special points the actual recursive Step One values agree across the lift. -/
theorem stepOneInvM_lifted_special {n r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (y : liftCMfd.{u} Y) (hs : IsSpecial M T ((liftDiffeomorph.{u} Y).symm y)) :
    Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily.{u} hn r)
      (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y =
    Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily.{0} hn r) M T ((liftDiffeomorph.{u} Y).symm y) := by
  have hb := coeffHomMarked_pullback_diffeo (liftDiffeomorph.{u} X).symm M hM.isCoherent hM.isClosedSubmanifold_N
  exact stepOneInvM_lifted_special_of_bar_base hn M hM T hT hb y hs

/-- The actual Step One level/special regime is preserved along the lift. -/
theorem stepRegime_liftTower {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (s : ℕ) (y : liftCMfd.{u} Y) :
    stepRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) s (liftTower.{u} T) y ↔
      stepRegime M s T ((liftDiffeomorph.{u} Y).symm y) := by
  have hb := coeffHomMarked_pullback_diffeo (liftDiffeomorph.{u} X).symm M hM.isCoherent hM.isClosedSubmanifold_N
  exact stepRegime_liftTower_of_bar_base M hM T hT hb s y

/-- The actual numeric run in a Step One regime is preserved. -/
theorem stepRegimeRun_liftTower {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (s : ℕ) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower (barMarked M) T → ∀ y : liftCMfd.{u} Y,
      StepOneRegime.regimeRun (stepRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) s) (liftTower.{u} T) y =
        StepOneRegime.regimeRun (stepRegime M s) T ((liftDiffeomorph.{u} Y).symm y)
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, y => by
    classical
    let z := (liftDiffeomorph.{u} _) (π ((liftDiffeomorph.{u} _).symm y))
    have hreg := stepRegime_liftTower M hM T hT.1 s z
    have hr := stepRegimeRun_liftTower M hM s T hT.1 z
    simp only [liftTower, StepOneRegime.regimeRun_step]
    change (if stepRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) s (liftTower.{u} T) z then
      StepOneRegime.regimeRun (stepRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) s) (liftTower.{u} T) z + 1 else 0) = _
    simpa only [z, Diffeomorph.symm_apply_apply] using (show
      (if stepRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) s (liftTower.{u} T) z then
        StepOneRegime.regimeRun (stepRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) s) (liftTower.{u} T) z + 1 else 0) =
      (if stepRegime M s T ((liftDiffeomorph.{u} _).symm z) then
        StepOneRegime.regimeRun (stepRegime M s) T ((liftDiffeomorph.{u} _).symm z) + 1 else 0) from by rw [hreg,hr])

/-- The literal Step One positive-level mask is the inverse image under the lift. -/
theorem maskA_liftTower {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (y : liftCMfd.{u} Y) :
    maskA (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y =
      G3UniverseOpenDiffeo.preimageOpens (liftDiffeomorph.{u} Y).symm
        (maskA M T ((liftDiffeomorph.{u} Y).symm y)) := by
  let e := (liftDiffeomorph.{u} Y).symm
  have hm : {z : liftCMfd.{u} Y |
      (∀ H ∈ origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T), z ∈ H → y ∈ H) ∧
        ¬ (level (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z =
          level (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y ∧
          IsSpecial (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z)} =
      e ⁻¹' {z : Y | (∀ H ∈ origMembers M T, z ∈ H → e y ∈ H) ∧
        ¬ (level M T z = level M T (e y) ∧ IsSpecial M T z)} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,origMembers_liftTower_barTest M hM T hT, List.forall_mem_map]
    rw [level_liftTower_barTest M hM T hT z, level_liftTower_barTest M hM T hT y,
      isSpecial_liftTower M hM T hT z]
  apply Opens.ext
  change interior _ = e ⁻¹' interior _
  rw [hm]
  exact (e.toHomeomorph.preimage_interior _).symm

/-- An actual bar-marked test history lifts as an actual bar-marked test history. -/
theorem barTest_liftTower {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T) :
    IsGeoTestTower (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T) := by
  have hb := coeffHomMarked_pullback_diffeo (liftDiffeomorph.{u} X).symm M hM.isCoherent hM.isClosedSubmanifold_N
  change IsGeoTestTower (HomogenizedIdealAlong.coeffMarkedAlong
    (HomogenizedIdealAlong.homMarkedAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M))) (liftTower.{u} T)
  rw [hb]
  exact HironakaG3UniverseLiftedTestHistory.liftTower_isGeoTestTower (barMarked M)
    (StepOneLowerDomain.isWellFormed_barMarked M hM) T hT
end
end Hironaka.G3UniverseStepOneSpecialActual

