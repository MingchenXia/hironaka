/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.HomogenizedAmbientMarkedDataExact
import Hironaka.Resolution.HironakaActualZeroSectionDifferentialIdeals
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.MarkedIdeal.HomogenizedIdealAlong

/-!
# Actual coefficient and homogenized marked ideals on the closed zero section

The entire original marked record commutes with genuine CLOSED zero-section
restriction through along-carrier homogenization and coefficient operations.
The same ordered boundary, derivative marks, finite sum exponents and product
mark are retained. Only general holomorphic pullback algebra is used; no
submersion, invariant-value or comparison-history certificate is assumed.
Canonical embedding independence and proper resolution descent remain open.
Blueprint: `hironaka-actual-zero-section-coefficient-ideals-extension.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualZeroSectionCoefficientIdeals
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualZeroCoordinateContactSeed
  HironakaActualZeroSectionDifferentialIdeals MarkedIdeals
  DerivativeIdeal DerivativeIdealAlong DerivativeIdealAlongCoherent
  HomogenizedIdealAlong HomogenizedIdeal HomogenizedEquivalence HomogenizedGlueing
  CoefficientIdeal IdealWeightPowers HironakaSmoothSubmersionCoefficientIdeals
  GermIdealPullbackCalculus
variable {n : ℕ}

private theorem homogenized_ideal (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (hJ : J.IsCoherent) (hZ : IsClosedSubmanifold (n+1) (zeroPlane n)) (μ : ℕ) :
    GermIdeal.pullback (m := n) (tangentInclusion n 1) (homogenizedIdealAlong (zeroPlane n) J μ)=
      homogenizedIdeal (GermIdeal.pullback (m := n) (tangentInclusion n 1) J) μ := by
  have hT : GermIdeal.pullback (m := n) (tangentInclusion n 1) (tangentIdealAlong (zeroPlane n) J μ)=
      tangentIdeal (GermIdeal.pullback (m := n) (tangentInclusion n 1) J) μ :=
    zero_section_iterDerivIdealAlong J hJ (μ-1)
  rw [homogenizedIdeal_eq_homSum]
  unfold homogenizedIdealAlong homSum
  rw [pullback_finSumIdeal (tangentInclusion n 1).contMDiff _ _ (fun i _ =>
    IdealWeightPowers.isCoherent_mul (isCoherent_iterDerivIdealAlong hJ hZ i)
      (isCoherent_idealPow (isCoherent_tangentIdealAlong hJ hZ μ) i))]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul (tangentInclusion n 1).contMDiff
    (isCoherent_iterDerivIdealAlong hJ hZ i) (isCoherent_idealPow (isCoherent_tangentIdealAlong hJ hZ μ) i),
    pullback_idealPow (tangentInclusion n 1).contMDiff (isCoherent_tangentIdealAlong hJ hZ μ),
    zero_section_iterDerivIdealAlong J hJ i,hT]
  rfl

private theorem coefficient_record (M : MarkedIdeal (n+1) (ComplexModel (n+1)))
    (hJ : M.ideal.IsCoherent) (hN : M.N=zeroPlane n)
    (hZ : IsClosedSubmanifold (n+1) (zeroPlane n)) :
    markedPullback (m := n) (tangentInclusion n 1) (coeffMarkedAlong M)=
      coeffMarked (markedPullback (m := n) (tangentInclusion n 1) M) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) (tangentInclusion n 1)
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
        (sumExp (fun j => M.d-j) M.d i)) M.d)=
    finSumIdeal (fun i => idealPow
      (iterDerivIdeal (GermIdeal.pullback (m := n) (tangentInclusion n 1) M.ideal) i)
      (sumExp (fun j => M.d-j) M.d i)) M.d
  rw [hN,pullback_finSumIdeal (tangentInclusion n 1).contMDiff _ _
    (fun i _ => isCoherent_idealPow (isCoherent_iterDerivIdealAlong hJ hZ i) _)]
  apply finSumIdeal_congr
  intro i _
  rw [pullback_idealPow (tangentInclusion n 1).contMDiff (isCoherent_iterDerivIdealAlong hJ hZ i),
    zero_section_iterDerivIdealAlong M.ideal hJ i]

/-- The entire homogenized marked record of the SAME original data on the
genuine closed zero plane, with the whole boundary/mark retained. -/
theorem zero_section_homMarkedAlong (M : MarkedIdeal (n+1) (ComplexModel (n+1)))
    (hM : M.IsWellFormed) (hN : M.N=zeroPlane n) :
    markedPullback (m := n) (tangentInclusion n 1) (homMarkedAlong M)=
      homMarked (markedPullback (m := n) (tangentInclusion n 1) M) := by
  have hZ : IsClosedSubmanifold (n+1) (zeroPlane n) := by
    rw [←hN]
    exact hM.isClosedSubmanifold_N
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) (tangentInclusion n 1) (homogenizedIdealAlong M.N M.ideal M.d)=_
  rw [hN]
  exact homogenized_ideal M.ideal hM.isCoherent hZ M.d

/-- Whole coefficient records agree with the SAME actual derivative marks,
finite sum exponents, literal product mark and every original boundary label. -/
theorem zero_section_coeffMarkedAlong (M : MarkedIdeal (n+1) (ComplexModel (n+1)))
    (hM : M.IsWellFormed) (hN : M.N=zeroPlane n) :
    markedPullback (m := n) (tangentInclusion n 1) (coeffMarkedAlong M)=
      coeffMarked (markedPullback (m := n) (tangentInclusion n 1) M) := by
  apply coefficient_record M hM.isCoherent hN
  rw [←hN]
  exact hM.isClosedSubmanifold_N

/-- The actual coefficient-after-homogenization composite uses this SAME
closed section and original record, before any invariant/history comparison. -/
theorem zero_section_coeff_homMarkedAlong (M : MarkedIdeal (n+1) (ComplexModel (n+1)))
    (hM : M.IsWellFormed) (hN : M.N=zeroPlane n) :
    markedPullback (m := n) (tangentInclusion n 1) (coeffMarkedAlong (homMarkedAlong M))=
      coeffMarked (homMarked (markedPullback (m := n) (tangentInclusion n 1) M)) := by
  have hZ : IsClosedSubmanifold (n+1) (zeroPlane n) := by
    rw [←hN]
    exact hM.isClosedSubmanifold_N
  rw [coefficient_record (homMarkedAlong M)
    (isCoherent_homMarkedAlong hM.isCoherent hM.isClosedSubmanifold_N) hN hZ,
    zero_section_homMarkedAlong M hM hN]

end
end Hironaka.HironakaActualZeroSectionCoefficientIdeals
