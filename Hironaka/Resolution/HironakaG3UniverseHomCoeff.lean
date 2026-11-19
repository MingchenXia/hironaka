import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Resolution.HironakaG3UniversePullbackPowers
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseBarMarked
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedIdealAlong
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniversePullbackPowers
  GermIdealPullbackCalculus IdealWeightPowers HomogenizedGlueing CoefficientIdeal
  DerivativeIdealAlong DerivativeIdealAlongEtale DerivativeIdealAlongCoherent GiraudAlong
  HomogenizedEquivalence
noncomputable section

/-- The existing étale iterated-derivative dictionary applies across independent universes. -/
theorem iterDeriv_pullback_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (N : Set X) (I : GermIdeal n X) (hI : I.IsCoherent) (j : ℕ) :
    GermIdeal.pullback (m := n) e (iterDerivIdealAlong N I j) =
      iterDerivIdealAlong (e ⁻¹' N) (GermIdeal.pullback (m := n) e I) j := by
  exact pullback_iterDerivIdealAlong_of_inverse
    (fun y => (e.contMDiff y).mdifferentiableAt (by simp))
    (fun x => (e.symm.contMDiff x).mdifferentiableAt (by simp))
    e.apply_symm_apply e.symm_apply_apply
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) j

/-- Homogenization commutes with an arbitrary holomorphic pullback when the iterated relative derivatives commute. -/
theorem homogenized_pullback_of_iter {n m : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (f : Y → X) (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (N : Set X) (I : GermIdeal n X) (hI : I.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hIter : ∀ j, GermIdeal.pullback (m := m) f (iterDerivIdealAlong N I j) =
      iterDerivIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) j) (μ : ℕ) :
    GermIdeal.pullback (m := m) f (homogenizedIdealAlong N I μ) =
      homogenizedIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ := by
  unfold homogenizedIdealAlong homSum
  rw [pullback_finSumIdeal hf _ _ (fun i _ =>
    IdealWeightPowers.isCoherent_mul (isCoherent_iterDerivIdealAlong hI hN i)
      (isCoherent_idealPow (isCoherent_tangentIdealAlong hI hN μ) i))]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaG3UniversePullbackPowers.pullback_mul hf
    (isCoherent_iterDerivIdealAlong hI hN i) (isCoherent_idealPow (isCoherent_tangentIdealAlong hI hN μ) i),
    HironakaG3UniversePullbackPowers.pullback_idealPow hf (isCoherent_tangentIdealAlong hI hN μ),
    hIter i]
  change _ = (iterDerivIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) i).mul
    (idealPow (iterDerivIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (μ-1)) i)
  rw [show GermIdeal.pullback (m := m) f (tangentIdealAlong N I μ) = _ from
    hIter (μ-1)]

/-- The coefficient record commutes with an arbitrary holomorphic pullback when the iterated relative derivatives commute. -/
theorem coeffMarked_pullback_of_iter {n m : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (f : Y → X) (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (hIter : ∀ j, GermIdeal.pullback (m := m) f (iterDerivIdealAlong M.N M.ideal j) =
      iterDerivIdealAlong (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal) j) :
    markedPullback (m := m) f (coeffMarkedAlong M) = coeffMarkedAlong (markedPullback (m := m) f M) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := m) f
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
        (sumExp (fun j => M.d-j) M.d i)) M.d) =
    finSumIdeal (fun i => idealPow (iterDerivIdealAlong (f ⁻¹' M.N)
      (GermIdeal.pullback (m := m) f M.ideal) i) (sumExp (fun j => M.d-j) M.d i)) M.d
  rw [pullback_finSumIdeal hf _ _
    (fun i _ => isCoherent_idealPow (isCoherent_iterDerivIdealAlong hI hN i) _)]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaG3UniversePullbackPowers.pullback_idealPow hf
    (isCoherent_iterDerivIdealAlong hI hN i), hIter i]

/-- The algebraic core applied to a cross-universe biholomorphism. -/
theorem homogenized_pullback_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (N : Set X) (I : GermIdeal n X) (hI : I.IsCoherent) (hN : IsClosedSubmanifold n N) (μ : ℕ) :
    GermIdeal.pullback (m := n) e (homogenizedIdealAlong N I μ) =
      homogenizedIdealAlong (e ⁻¹' N) (GermIdeal.pullback (m := n) e I) μ :=
  homogenized_pullback_of_iter e e.contMDiff N I hI hN (iterDeriv_pullback_diffeo e N I hI) μ

/-- The coefficient core applied to a cross-universe biholomorphism. -/
theorem coeffMarked_pullback_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N) :
    markedPullback (m := n) e (coeffMarkedAlong M) = coeffMarkedAlong (markedPullback (m := n) e M) :=
  coeffMarked_pullback_of_iter e e.contMDiff M hI hN (iterDeriv_pullback_diffeo e M.N M.ideal hI)

/-- Actual bar-marked pullback along a cross-universe biholomorphism. -/
theorem coeffHomMarked_pullback_diffeo {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N) :
    coeffMarkedAlong (homMarkedAlong (markedPullback (m := n) e M)) =
      markedPullback (m := n) e (coeffMarkedAlong (homMarkedAlong M)) := by
  have hHom : markedPullback (m := n) e (homMarkedAlong M) = homMarkedAlong (markedPullback (m := n) e M) := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
    exact homogenized_pullback_diffeo e M.N M.ideal hI hN M.d
  rw [← hHom, ← coeffMarked_pullback_diffeo e (homMarkedAlong M) (isCoherent_homMarkedAlong hI hN) hN]
end
end Hironaka.G3UniverseBarMarked
