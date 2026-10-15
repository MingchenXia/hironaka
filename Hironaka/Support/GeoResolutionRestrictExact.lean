/- Complete original actual resolution open-restriction proof. -/
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealRestrictOpen

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.NormalCrossingsInvariance
  Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism
  Hironaka.GermIdealPullbackCalculus Hironaka.GermIdealOrder
  Hironaka.IdealWeightPowers Hironaka.RestrictedIdealExtension
  Hironaka.RestrictedIdealQuotient Hironaka.InvertibleIdealQuotient
  Hironaka.GermIdealTotalTransform Hironaka.BlowupStrictSubmanifold
  Hironaka.BlowupRestrictOpen Hironaka.BlowupTowerTransforms

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n} (U : Opens X) {𝔪 : MarkedIdeal n X}
/-- **Resolutions restrict**: the restriction to `U` of a resolution of `𝔪` is a resolution of `𝔪|_U`. -/
theorem isGeoResolution_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoResolution 𝔪 T) :
    IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT.1
  refine ⟨isGeoTestTower_restrict U hN h𝔞 T hT.1, ?_⟩
  rw [geoTransformAlong_restrict U hN h𝔞 T hT.1, cosupp_pullback_val _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg), hT.2,
    preimage_empty]

end
end Hironaka.MarkedIdealRestrictOpen
