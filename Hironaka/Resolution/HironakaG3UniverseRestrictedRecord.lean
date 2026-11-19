import Hironaka.Resolution.HironakaG3UniverseOpenDiffeo
import Hironaka.Resolution.HironakaG3UniverseGeoTransformBase
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseRestrictedRecord
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaSmoothSubmersionCoefficientIdeals
  G3UniverseOpenDiffeo HironakaSmoothSubmersionContactParameterCoefficientIdeals
noncomputable section

/-- Restricting a pulled-back record agrees with pulling back its literal restriction. -/
theorem markedPullback_restrict_diffeo {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) (U : Opens X) :
    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : preimageOpens e U → Y) (markedPullback (m := n) e M) =
    markedPullback (m := n) (preimageDiffeo e U).symm
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) := by
  change markedPullback (m := n) (Subtype.val : preimageOpens e U → Y) (markedPullback (m := n) e M) =
    markedPullback (m := n) (preimageDiffeo e U).symm
      (markedPullback (m := n) (Subtype.val : U → X) M)
  have hl := whole_parameter_markedPullback_comp (X := X) (Y := Y)
    (Z := CMfd.of (n := n) (preimageOpens e U)) e.contMDiff contMDiff_subtype_val M hM
  have hr := whole_parameter_markedPullback_comp (X := X) (Y := CMfd.of (n := n) U)
    (Z := CMfd.of (n := n) (preimageOpens e U)) contMDiff_subtype_val
      (preimageDiffeo e U).symm.contMDiff M hM
  rw [← hl, ← hr]
  rfl
end
end Hironaka.G3UniverseRestrictedRecord
