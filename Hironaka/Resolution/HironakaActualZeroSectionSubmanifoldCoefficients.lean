/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualZeroSectionSubmanifoldDifferentials

/-!
# Entire marked coefficient data on an arbitrary original closed carrier lift

The same closed section and independently lifted original closed regular
carrier retain the whole along-homogenized ideal, homogenized marked record,
coefficient marked record and their actual composite. The original derivative
marks, powers, finite sums and every boundary position remain literal. Only
original carrier geometry and ideal coherence are inputs; no pullback-boundary
wellformedness, target differential, canonical-value or history certificate is
assumed. Cross-ambient canonical embedding independence remains open.
Blueprint: `hironaka-actual-zero-section-submanifold-coefficients-extension.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualZeroSectionSubmanifoldCoefficients
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualZeroSectionSubmanifoldDifferentials
  MarkedIdeals DerivativeIdealAlong DerivativeIdealAlongCoherent
  HomogenizedIdealAlong HomogenizedGlueing HomogenizedEtale HomogenizedEquivalence
  CoefficientIdeal IdealWeightPowers HironakaSmoothSubmersionCoefficientIdeals
  GermIdealPullbackCalculus
variable {n : ℕ}

/-- Entire along-carrier homogenization through the SAME closed section. -/
theorem zero_section_submanifold_homogenizedIdealAlong {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (hJ : J.IsCoherent) (μ : ℕ) :
    GermIdeal.pullback (m := n) (tangentInclusion n 1) (homogenizedIdealAlong (liftedCarrier A) J μ)=
      homogenizedIdealAlong A (GermIdeal.pullback (m := n) (tangentInclusion n 1) J) μ := by
  have hLift := liftedCarrier_closed_submanifold hA
  have hT : GermIdeal.pullback (m := n) (tangentInclusion n 1)
      (tangentIdealAlong (liftedCarrier A) J μ)=
        tangentIdealAlong A (GermIdeal.pullback (m := n) (tangentInclusion n 1) J) μ :=
    zero_section_submanifold_iterDerivIdealAlong hA J hJ (μ-1)
  unfold homogenizedIdealAlong homSum
  rw [pullback_finSumIdeal (tangentInclusion n 1).contMDiff _ _ (fun i _ =>
    IdealWeightPowers.isCoherent_mul (isCoherent_iterDerivIdealAlong hJ hLift i)
      (isCoherent_idealPow (isCoherent_tangentIdealAlong hJ hLift μ) i))]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul (tangentInclusion n 1).contMDiff
    (isCoherent_iterDerivIdealAlong hJ hLift i)
      (isCoherent_idealPow (isCoherent_tangentIdealAlong hJ hLift μ) i),
    pullback_idealPow (tangentInclusion n 1).contMDiff (isCoherent_tangentIdealAlong hJ hLift μ),
    zero_section_submanifold_iterDerivIdealAlong hA J hJ i,hT]

private theorem pullback_carrier_eq {A : Set (ComplexModel n)}
    (M : MarkedIdeal (n+1) (ComplexModel (n+1))) (hN : M.N=liftedCarrier A) :
    (markedPullback (m := n) (tangentInclusion n 1) M).N=A := by
  change tangentInclusion n 1 ⁻¹' M.N=A
  rw [hN]
  ext x
  exact section_mem_liftedCarrier_iff A x

/-- Equality of ALL marked fields, with the same ordered original boundary
and marking; no wellformedness of the pulled-back boundary is presumed. -/
theorem zero_section_submanifold_homMarkedAlong {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) (M : MarkedIdeal (n+1) (ComplexModel (n+1)))
    (hJ : M.ideal.IsCoherent) (hN : M.N=liftedCarrier A) :
    markedPullback (m := n) (tangentInclusion n 1) (homMarkedAlong M)=
      homMarkedAlong (markedPullback (m := n) (tangentInclusion n 1) M) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) (tangentInclusion n 1)
      (homogenizedIdealAlong M.N M.ideal M.d)=
    homogenizedIdealAlong (markedPullback (m := n) (tangentInclusion n 1) M).N
      (GermIdeal.pullback (m := n) (tangentInclusion n 1) M.ideal) M.d
  rw [pullback_carrier_eq M hN,hN]
  exact zero_section_submanifold_homogenizedIdealAlong hA M.ideal hJ M.d

/-- Actual coefficient marked data retain every original derivative mark,
literal finite sum exponent, product marking and boundary position. -/
theorem zero_section_submanifold_coeffMarkedAlong {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) (M : MarkedIdeal (n+1) (ComplexModel (n+1)))
    (hJ : M.ideal.IsCoherent) (hN : M.N=liftedCarrier A) :
    markedPullback (m := n) (tangentInclusion n 1) (coeffMarkedAlong M)=
      coeffMarkedAlong (markedPullback (m := n) (tangentInclusion n 1) M) := by
  have hLift := liftedCarrier_closed_submanifold hA
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) (tangentInclusion n 1)
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
        (sumExp (fun j => M.d-j) M.d i)) M.d)=
    finSumIdeal (fun i => idealPow
      (iterDerivIdealAlong (markedPullback (m := n) (tangentInclusion n 1) M).N
        (GermIdeal.pullback (m := n) (tangentInclusion n 1) M.ideal) i)
      (sumExp (fun j => M.d-j) M.d i)) M.d
  rw [pullback_carrier_eq M hN,hN,pullback_finSumIdeal (tangentInclusion n 1).contMDiff _ _
    (fun i _ => isCoherent_idealPow (isCoherent_iterDerivIdealAlong hJ hLift i) _)]
  apply finSumIdeal_congr
  intro i _
  rw [pullback_idealPow (tangentInclusion n 1).contMDiff (isCoherent_iterDerivIdealAlong hJ hLift i),
    zero_section_submanifold_iterDerivIdealAlong hA M.ideal hJ i]

/-- The SAME actual coefficient-after-homogenization composite commutes
with the closed section before any canonical-value or history comparison. -/
theorem zero_section_submanifold_coeff_homMarkedAlong {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) (M : MarkedIdeal (n+1) (ComplexModel (n+1)))
    (hJ : M.ideal.IsCoherent) (hN : M.N=liftedCarrier A) :
    markedPullback (m := n) (tangentInclusion n 1) (coeffMarkedAlong (homMarkedAlong M))=
      coeffMarkedAlong (homMarkedAlong (markedPullback (m := n) (tangentInclusion n 1) M)) := by
  have hNreg : IsClosedSubmanifold (n+1) M.N := by
    rw [hN]
    exact liftedCarrier_closed_submanifold hA
  rw [zero_section_submanifold_coeffMarkedAlong hA (homMarkedAlong M)
    (isCoherent_homMarkedAlong hJ hNreg) hN,
    zero_section_submanifold_homMarkedAlong hA M hJ hN]

end
end Hironaka.HironakaActualZeroSectionSubmanifoldCoefficients
