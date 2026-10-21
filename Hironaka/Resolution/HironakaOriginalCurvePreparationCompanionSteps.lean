/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalDiscretePositiveCompanion
/-! Original-only whole-curve preparation projection supplies every actual
positive local companion test, preserving the SAME projection and original prefix. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCurvePreparationCompanionSteps
noncomputable section
open HironakaOriginalDiscretePositiveCompanion
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupRestrictOpen
  NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong CompanionOpen
  InvDomainCompanion MonomialPartAlong NonmonomialTransformAlong
  MarkedIdealOperationsAlong RestrictedIdealExtension DivisorExponentAlong
  HomogenizedIdealAlong GermIdealOrder
open HironakaOriginalSmoothCurveWholeTupleBadBlowup HironakaOneDimensionalCanonicalSuperlevels
  CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- ONLY original curve/domain/canonical-prefix and genuine coherent family
internally produce ONE global preparation map and every positive local companion. -/
theorem exists_original_curve_preparation_positive_companion_steps :
    ∀
    {t : ℕ} {X Y : CMfd.{u} (1+t)} (k : ℕ)
    (M : MarkedIdeal (1+t) X) (_hM : IsInvDomain (k+1) M) (T : BlowupTower X Y)
    (_hcan : IsCanonical M (fun {D : CMfd.{u} (1+t)} (Q : BlowupTower X D) (x : D) =>
      (invFamily (by omega : 0<1+t) (k+1)).inv M Q x) T)
    {S : Set Y} (_hS : IsComplexAnalyticSubset (n := 1+t) S)
    (_hreg : ∀ x ∈ S,RegularAtDim (n := 1+t) S x 1) (_hSP : S ⊆ (geoTransformAlong M T).cosupp)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal (1+t) Y) (_hA : ∀ i,(A i).IsCoherent),
    let C := actualOriginalCurveWholeBad (X := X) (Y := Y) (k+1) M T A S
    ∃ (Z : CMfd.{u} (1+t)) (π : Z → Y) (hπ : IsBlowupAlong (1+t) C π) (_hholo : ContMDiff 𝓘(ℂ,ComplexModel (1+t)) 𝓘(ℂ,ComplexModel (1+t)) ∞ π),
      IsGeoTestTower M (BlowupTower.step (X := X) (Y := Y) (Z := Z) T C π hπ) ∧ IsInvDomain (k+1) (geoTransformAlong M (BlowupTower.step (X := X) (Y := Y) (Z := Z) T C π hπ)) ∧
      IsProperMap π ∧ IsIsomorphismOver (1+t) π Cᶜ ∧
      ∀ c ∈ C,1 ≤ nmOrd (M := Y) (geoTransformAlong M T) c →
        ∃ U : Opens Y,c ∈ U ∧ (U : Set Y) ∩ C={c} ∧
          let J : MarkedIdeal (1+t) (CMfd.of (n := 1+t) U) :=
            MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong M T)
          let O := companionOf (1+t) J (nmOrd (M := Y) (geoTransformAlong M T) c)
          let V : Opens Z := ⟨π ⁻¹' (U : Set Y),U.isOpen.preimage hπ.contMDiff.continuous⟩
          let ρ : V → U := fun y => ⟨π y,y.property⟩
          let D : Set U := (Subtype.val : U → Y) ⁻¹' C
          IsInvDomain (k+1) O ∧ IsMaximalOrderAlong O.N O.ideal O.d ∧
            ∃ hρ : IsBlowupAlong (1+t) D ρ,
              IsGeoTestTower O (BlowupTower.step (X := CMfd.of (n := 1+t) U)
                (Y := CMfd.of (n := 1+t) U) (Z := CMfd.of (n := 1+t) V) .refl D ρ hρ) ∧
              IsInvDomain (k+1) (O.geoTransform D ρ) ∧
              (O.geoTransform D ρ).cosupp=
                ordGe (M := CMfd.of (n := 1+t) V) (J.geoTransform D ρ)
                  (nmOrd (M := Y) (geoTransformAlong M T) c) ∩ (J.geoTransform D ρ).cosupp := by
  intro t X Y k M hM T hcan S hS hreg hSP ι hι A hA
  have hn : 0<1+t := by omega
  obtain ⟨hCa,hdC,hCadm,_hregC,_hlocal⟩ :=
    original_smooth_curve_whole_tuple_bad_admissible (k+1) M hM T hcan hS hreg hSP A hA
  obtain ⟨Z,π,hπ,hstep,hpost,hproper,hholo,hiso,_hSNC⟩ :=
    exists_original_smooth_curve_whole_tuple_bad_blowup (k+1) M hM T hcan hS hreg hSP A hA
  have hT : IsGeoTestTower M T := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hcan
  have hlocals := fun (c : Y) (hc : c ∈ actualOriginalCurveWholeBad (X := X) (Y := Y) (k+1) M T A S)
      (hq : 1 ≤ nmOrd (M := Y) (geoTransformAlong M T) c) =>
    original_test_prefix_discrete_positive_companion_step (n := 1+t) (k := k+1)
      (X := X) (Y := Y) (Z := Z) hn M hM T hT hCadm
      (isDiscrete_of_analytic_dimLE_zero hCa hdC) hc hq hπ
  exact ⟨Z,π,hπ,hholo,hstep,hpost,hproper,hiso,hlocals⟩

end
end Hironaka.HironakaOriginalCurvePreparationCompanionSteps
