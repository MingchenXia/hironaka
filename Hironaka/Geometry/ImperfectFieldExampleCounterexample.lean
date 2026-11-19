/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Geometry.ImperfectFieldExampleFunctionField
import Hironaka.Geometry.ImperfectFieldExampleClosedPoint
import Hironaka.Geometry.AlterationBasic
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.FieldTheory.Perfect

/-!
# The precise imperfect-field regular-curve counterexample of de Jong 2.10

The dimension-comparison proofs are extracted unchanged (apart from namespace)
from `EnvelopeProperty/AlgGeom/KrullDim.lean` (SHA256
`804535bd109a31ba7f281774b390f82f0c49a064e2be34f090ebb7cdfd71c815`)
and `EnvelopeProperty/AlgGeom/ProjectionNoether.lean` (SHA256
`a748c3343f786907107270e576d701395f66020e14595a41095def07b7b0ada4`).
Only the actual algebraic going-up/incomparability proofs are reused.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Polynomial
open Hironaka.Algebra.ImperfectFieldExample
open Hironaka.Geometry.ImperfectFieldExampleCurve
open Hironaka.Geometry.ImperfectFieldExampleFunctionField
open Hironaka.Geometry.ImperfectFieldExampleClosedPoint

namespace Hironaka.Geometry.ImperfectFieldExampleCounterexample

theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  let := f.toAlgebra
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f) fun P Q hPQ => ?_
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (show P.asIdeal < Q.asIdeal from hPQ)
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hPQ.le ⟨hxQ, hxP⟩ (hf x)

theorem ringKrullDim_le_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R ≤ ringKrullDim S := by
  algebraize [f]
  have : Algebra.IsIntegral R S := ⟨hf⟩
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hPp, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S) l.head.asIdeal ⊥
    (by
      rw [Ideal.comap_bot_of_injective (algebraMap R S) hinj]
      exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPc.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

theorem curveRing_ringKrullDim : ringKrullDim CurveRing = 1 := by
  let : Module.Finite CoefficientRing CurveRing := quadraticEquation_monic.finite_adjoinRoot
  have hint : (algebraMap CoefficientRing CurveRing).IsIntegral :=
    algebraMap_isIntegral_iff.mpr inferInstance
  have hinj : Function.Injective (algebraMap CoefficientRing CurveRing) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (f := quadraticEquation)
      (by rw [degree_eq_natDegree quadraticEquation_monic.ne_zero]; simp [quadraticEquation])
  have hdim : ringKrullDim CoefficientRing = 1 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  apply le_antisymm
  · exact (ringKrullDim_le_of_isIntegral _ hint).trans_eq hdim
  · exact hdim ▸ ringKrullDim_le_of_isIntegral_of_injective _ hint hinj

theorem specCurve_dimension_one : topologicalKrullDim (Spec (.of CurveRing)) = 1 := by
  change topologicalKrullDim (PrimeSpectrum CurveRing) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, curveRing_ringKrullDim]

instance curveStructure_isVariety : IsVariety curveStructure := .mk

theorem baseField_not_perfect : ¬ PerfectField BaseField := by
  intro h
  let : PerfectField BaseField := h
  obtain ⟨b, hb⟩ := surjective_frobenius BaseField 3 alpha
  exact alpha_not_cube b hb

/-- All source-specific assertions use the actual explicit curve and its native structure map. -/
theorem regular_nonsmooth_separable_curve :
    ¬ PerfectField BaseField ∧ IsVariety curveStructure ∧
      IsRegularScheme (Spec (.of CurveRing)) ∧
      topologicalKrullDim (Spec (.of CurveRing)) = 1 ∧
      SeparableGenericSmoothness.FunctionFieldSeparablyGenerated curveStructure ∧
      ¬ Smooth curveStructure ∧
      ∃ z : Spec (.of CurveRing), IsClosed ({z} : Set (Spec (.of CurveRing))) ∧
        z ∉ curveStructure.smoothLocus :=
  ⟨baseField_not_perfect, inferInstance, specCurve_isRegular, specCurve_dimension_one,
    curveFunctionFieldSeparablyGenerated, curveStructure_not_smooth, exists_closed_nonsmooth_point⟩

end Hironaka.Geometry.ImperfectFieldExampleCounterexample
