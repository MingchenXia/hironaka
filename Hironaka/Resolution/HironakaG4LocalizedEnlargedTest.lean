import Hironaka.Resolution.HironakaG4ToricEnlargedTest
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen

/-! Test an enlarged boundary only over the source window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4LocalizedEnlargedTest
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings MarkedIdealOpenBiholomorphism MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  GermIdealOrder RelativePrincipalizationSpan BlowupRestrictOpen

variable {n : ℕ} {X : CMfd.{u} n}

/-- Normal-crossings data at every centre of this particular history. -/
def LocalBoundaryHistory (D : MarkedIdeal n X) (U : Opens X) :
    ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => LocalBoundaryHistory D U T ∧
      HasNormalCrossings n ((Subtype.val : openPreimage T U → _) ⁻¹' C)
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T)).E

/-- If the enlarged zero-marked record is well formed over a window and every
smaller test centre has normal crossings there with the transformed enlarged
boundary, the restricted history tests that enlarged record. -/
theorem restricted_enlarged_test_of_local_nc
    (P D : MarkedIdeal n X) (hPN : P.N ⊆ D.N) (U : Opens X)
    (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed) (hmark : D.d = 0) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower P T → LocalBoundaryHistory D U T →
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T) := by
  intro Y T
  induction T with
  | refl => intro _ _; trivial
  | @step Y Z T C π hπ ih =>
    intro hTest hNC
    have hprefix : IsGeoTestTower P T := hTest.1
    have hDprefix := ih hprefix hNC.1
    have hwell := isWellFormed_geoTransformAlong hD (restrict U T) hDprefix
    have hmark' : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T)).d = 0 := by
      simp [MarkedIdeal.pullback, hmark, d_geoTransformAlong]
    refine ⟨hDprefix, isClosedSubmanifold_preimage_val hπ.1 (openPreimage T U), ?_, hNC.2⟩
    have hCN : C ⊆ strictAlong T D.N := by
      have hc := hTest.2.subset_N
      rw [N_geoTransformAlong] at hc
      exact hc.trans (MemberInterTowerAlong.strictAlong_mono T hPN)
    rw [show (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T)).cosupp =
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T)).N by
      change cosupport n _ _ _ = _
      rw [hmark', cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hwell.isCoherent hg)]]
    rw [N_geoTransformAlong, show (MarkedIdeal.pullback (Subtype.val : U → X) D).N =
      (Subtype.val : U → X) ⁻¹' D.N from rfl, strictAlong_restrict U T D.N]
    exact fun x hx => hCN hx

end
end Hironaka.HironakaG4LocalizedEnlargedTest
