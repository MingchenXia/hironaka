/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.FactorizationAmbientExact
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Blowup.BlowupTowerTransforms

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaControlledTransform
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupControlledTransform BlowupExceptionalDivisor InvertibleIdealQuotient IdealWeightPowers FactorizationFromResolution
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}
/-- **The controlled transforms along a tower** (mark one): `𝔞^c = 𝔞` on the base and, after a blowup `π` with exceptional
divisor `D`, `(π^* 𝔞^c : 𝓘_D)`. -/
def controlledTransformAlong (𝔞 : GermIdeal n X) : {Y : CMfd.{u} n} → BlowupTower X Y → GermIdeal n Y
  | _, .refl => 𝔞
  | _, .step T _ π hπ =>
      colon (GermIdeal.pullback (m := n) π (controlledTransformAlong 𝔞 T)) (exceptionalDivisor hπ).ideal

@[simp] theorem controlledTransformAlong_refl (𝔞 : GermIdeal n X) :
    controlledTransformAlong 𝔞 (BlowupTower.refl : BlowupTower X X) = 𝔞 := rfl

theorem controlledTransformAlong_step (𝔞 : GermIdeal n X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    controlledTransformAlong 𝔞 (.step T C π hπ) =
      colon (GermIdeal.pullback (m := n) π (controlledTransformAlong 𝔞 T)) (exceptionalDivisor hπ).ideal := rfl

/-- **The controlled transforms are the ideals of the ambient transforms**: along a multiple test blow-up `T` of the ambient
marked ideal `(X, X, E, 𝔞, 1)` (`𝔞` coherent), `𝔞^c_T` is the ideal of its transform. -/
theorem controlledTransformAlong_eq (𝔪 : MarkedIdeal n X) (hd : 𝔪.d = 1) (h𝔞 : 𝔪.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (ambient 𝔪) T →
      controlledTransformAlong 𝔪.ideal T = (geoTransformAlong (ambient 𝔪) T).ideal
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, -⟩ := (isGeoTestTower_step_iff (ambient 𝔪) T C π hπ).mp hT
      obtain ⟨hNT, hcohT, -⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T hTT
      have ih := controlledTransformAlong_eq 𝔪 hd h𝔞 T hTT
      rw [controlledTransformAlong_step, ih, geoTransformAlong_step,
        geoTransform_ideal_eq_controlledTransform hNT hcohT hπ, d_geoTransformAlong, ambient_d, hd]
      show _ = colon _ (idealPow (exceptionalDivisor hπ).ideal 1)
      rw [idealPow_one_of_isCoherent (isCoherent_ideal (exceptionalDivisor hπ))]

end
end Hironaka.HironakaControlledTransform
