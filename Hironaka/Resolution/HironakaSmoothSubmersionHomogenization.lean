/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.MarkedIdeal.HomogenizedEquivalence
import Hironaka.MarkedIdeal.HomogenizedAmbientMarkedDataExact
import Hironaka.MarkedIdeal.HomogenizedAmbientCoherenceExact
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionHomogenization
open Hironaka.HolomorphicIdealSheaves
open RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
open GermIdealOrder IdealWeightPowers HomogenizedIdeal HomogenizedEquivalence HomogenizedGlueing
open DerivativeIdeal DerivativeIdealTower HironakaSmoothSubmersionDerivativeEquality
open HironakaSmoothSubmersionCoefficientIdeals MarkedIdeals
open Hironaka
noncomputable section
variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
 [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
variable {f : Y → X}
variable (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)

include hf hh

theorem pullback_tangentIdeal {I : GermIdeal n X} (hI : I.IsCoherent) (μ : ℕ) :
 GermIdeal.pullback (m := m) f (tangentIdeal I μ) = tangentIdeal (GermIdeal.pullback (m := m) f I) μ := by
 exact (iterDerivIdeal_pullback_eq
   (fun y => hf.isSubmersionAt y) (fun y => hh.contMDiffAt.mdifferentiableAt (by simp))
   (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) (μ-1)).symm

theorem pullback_homogenized_summand {I : GermIdeal n X} (hI : I.IsCoherent) (μ i : ℕ) :
 GermIdeal.pullback (m := m) f ((iterDerivIdeal I i).mul (idealPow (tangentIdeal I μ) i)) =
   (iterDerivIdeal (GermIdeal.pullback (m := m) f I) i).mul
     (idealPow (tangentIdeal (GermIdeal.pullback (m := m) f I) μ) i) := by
 have ht : (tangentIdeal I μ).IsCoherent := isCoherent_iterDerivIdeal hI (μ-1)
 have hd := iterDerivIdeal_pullback_eq
   (fun y => hf.isSubmersionAt y) (fun y => hh.contMDiffAt.mdifferentiableAt (by simp))
   (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) i
 rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hh (isCoherent_iterDerivIdeal hI i)
   (isCoherent_idealPow ht i), pullback_idealPow hh ht i, ← hd, pullback_tangentIdeal hf hh hI μ]

theorem pullback_homogenizedIdeal {I : GermIdeal n X} (hI : I.IsCoherent) (μ : ℕ) :
 GermIdeal.pullback (m := m) f (homogenizedIdeal I μ) =
   homogenizedIdeal (GermIdeal.pullback (m := m) f I) μ := by
 change GermIdeal.pullback (m := m) f
   (finSumIdeal (fun i => (iterDerivIdeal I i).mul (idealPow (tangentIdeal I μ) i)) μ) =
     finSumIdeal (fun i => (iterDerivIdeal (GermIdeal.pullback (m := m) f I) i).mul
       (idealPow (tangentIdeal (GermIdeal.pullback (m := m) f I) μ) i)) μ
 have ht : (tangentIdeal I μ).IsCoherent := isCoherent_iterDerivIdeal hI (μ-1)
 rw [pullback_finSumIdeal hh
   (fun i => (iterDerivIdeal I i).mul (idealPow (tangentIdeal I μ) i)) μ
   (fun i _ => isCoherent_mul (isCoherent_iterDerivIdeal hI i) (isCoherent_idealPow ht i))]
 congr 1
 funext i
 exact pullback_homogenized_summand hf hh hI μ i

theorem homMarked_pullback_eq (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
 homMarked (markedPullback (m := m) f M) = markedPullback (m := m) f (homMarked M) := by
 have he := pullback_homogenizedIdeal hf hh hI M.d
 cases M
 simp only [homMarked, markedPullback]
 congr 1
 exact he.symm

theorem coeffHomMarked_pullback_eq (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
 CoefficientIdeal.coeffMarked (homMarked (markedPullback (m := m) f M)) =
   markedPullback (m := m) f (CoefficientIdeal.coeffMarked (homMarked M)) := by
 rw [homMarked_pullback_eq hf hh M hI]
 exact coeffMarked_pullback_eq hf hh _ (isCoherent_homogenizedIdeal hI M.d)

theorem homMarked_cosupport_pullback_eq (M : MarkedIdeal n X)
 (hN : M.N = univ) (hI : M.ideal.IsCoherent) :
 (homMarked (markedPullback (m := m) f M)).cosupp = f ⁻¹' (homMarked M).cosupp := by
 rw [homMarked_pullback_eq hf hh M hI]
 simpa only [MarkedIdeal.cosupp, markedPullback, homMarked, hN, preimage_univ] using
   HironakaSmoothSubmersionOrder.cosupport_pullback_eq hf (isCoherent_homogenizedIdeal hI M.d) M.d

theorem coeffHomMarked_cosupport_pullback_eq (M : MarkedIdeal n X)
 (hN : M.N = univ) (hI : M.ideal.IsCoherent) :
 (CoefficientIdeal.coeffMarked (homMarked (markedPullback (m := m) f M))).cosupp =
   f ⁻¹' (CoefficientIdeal.coeffMarked (homMarked M)).cosupp := by
 rw [homMarked_pullback_eq hf hh M hI]
 exact coefficient_cosupport_pullback_eq hf hh _ hN (isCoherent_homogenizedIdeal hI M.d)
end
end Hironaka.HironakaSmoothSubmersionHomogenization
