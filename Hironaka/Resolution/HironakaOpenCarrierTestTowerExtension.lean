/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaCoherentTransformExtension
import Hironaka.Resolution.HironakaStepOneMemberTailExtension

/-!
# Actual test histories extend from an original open containing their carrier

Only original whole-record equality on the open and original boundary equality
are inputs. Parent testness and all current centre cosupport conditions are
constructed along the SAME actual history, rather than assumed.
Blueprint: `hironaka-open-carrier-test-tower-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOpenCarrierTestTowerExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HironakaCoherentTransformExtension
  HomogenizedGlueingTower MemberInterTowerAlong NormalCrossings
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Original entire record equality is transported by the actual SAME restricted tower. -/
theorem current_open_record_eq (A B : MarkedIdeal n X) (G : Opens X)
    (hA : IsClosedSubmanifold n A.N) (hB : IsClosedSubmanifold n B.N)
    (hIA : A.ideal.IsCoherent) (hIB : B.ideal.IsCoherent)
    (hEq : MarkedIdeal.pullback (Subtype.val : G → X) A=
      MarkedIdeal.pullback (Subtype.val : G → X) B)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T) :
    MarkedIdeal.pullback (Subtype.val : openPreimage T G → Y) (geoTransformAlong A T)=
      MarkedIdeal.pullback (Subtype.val : openPreimage T G → Y) (geoTransformAlong B T) := by
  rw [←geoTransformAlong_restrict G hA hIA T hTA,
    ←geoTransformAlong_restrict G hB hIB T hTB,hEq]

/-- Parent testness is internally derived at EVERY actual chronological step. -/
theorem isGeoTestTower_parent (A B : MarkedIdeal n X) (G : Opens X)
    (hA : IsClosedSubmanifold n A.N) (hB : IsClosedSubmanifold n B.N)
    (hIA : A.ideal.IsCoherent) (hIB : B.ideal.IsCoherent)
    (hEq : MarkedIdeal.pullback (Subtype.val : G → X) A=
      MarkedIdeal.pullback (Subtype.val : G → X) B)
    (hAG : A.N ⊆ G) (hE : A.E=B.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower A T → IsGeoTestTower B T
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hT => by
    obtain ⟨hTA,hC⟩ := hT
    have hTB := isGeoTestTower_parent A B G hA hB hIA hIB hEq hAG hE T hTA
    have he := current_open_record_eq A B G hA hB hIA hIB hEq T hTA hTB
    have hcohA := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hA hIA T hTA).2
    have hcohB := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hB hIB T hTB).2
    have hCE : HasNormalCrossings n C (geoTransformAlong B T).E := by
      rw [←geoTransformAlong_E_eq_of_E_eq hE T]
      exact hC.2.2
    refine ⟨hTB,hC.1,?_,hCE⟩
    intro y hy
    have hCarrier : y∈strictAlong T A.N := by
      rw [←N_geoTransformAlong A T]
      exact (geoTransformAlong A T).cosupp_subset_N (hC.2.1 hy)
    have hyG : T.proj y∈G := hAG (strictAlong_subset_preimage T hA.1 hCarrier)
    let p : openPreimage T G := ⟨y,hyG⟩
    have hp : p∈(MarkedIdeal.pullback (Subtype.val : openPreimage T G → _) (geoTransformAlong A T)).cosupp := by
      rw [cosupp_pullback_val (geoTransformAlong A T)
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcohA hg)]
      exact hC.2.1 hy
    rw [he,cosupp_pullback_val (geoTransformAlong B T)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcohB hg)] at hp
    exact hp

end
end Hironaka.HironakaOpenCarrierTestTowerExtension
