import DeJongAlterations.Algebra.NodeFieldSeriesJetScalar
import DeJongAlterations.Algebra.NodeFieldQuadraticSource
import Mathlib.RingTheory.TensorProduct.Quotient

/-! Scalar extension of the ACTUAL native finite jets of an original formal equation. -/

noncomputable section

open MvPowerSeries TensorProduct IsLocalRing

namespace DeJongAlterations.Algebra.NodeFieldSeriesJetEquation

open NodeFormalMorse NodeVariableMorse NodeFieldSeriesJetFrame
  NodeFieldSeriesJetScalar NodeFieldQuadraticSource

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u v
variable (K : Type u) [Field K]

/-- The ENTIRE actual original equation ideal inside its SAME finite ambient jet. -/
def equationJetIdeal (f : Series K) (n : ℕ) : Ideal (Jet K n) :=
  (Ideal.span {f}).map (Ideal.Quotient.mk (variableIdeal K ^ n))

abbrev TruncatedEquation (f : Series K) (n : ℕ) :=
  Jet K n ⧸ equationJetIdeal K f n

/-- Commuting the two actual quotients identifies the native original equation jet. -/
def nativeJetEquiv (f : Series K) (hf : constantCoeff f = 0) (n : ℕ) :
    letI := equationLocalRing K f hf
    (Equation f ⧸ maximalIdeal (Equation f) ^ n) ≃ₐ[K] TruncatedEquation K f n := by
  let := equationLocalRing K f hf
  exact (Ideal.quotientEquivAlgOfEq K (equation_variable_pow_map K f hf n).symm).trans
    (DoubleQuot.quotQuotEquivCommₐ K (Ideal.span {f}) (variableIdeal K ^ n))

/-- EVERY original series representative survives BOTH actual quotient operations unchanged. -/
theorem nativeJetEquiv_mk (f : Series K) (hf : constantCoeff f = 0) (n : ℕ) (a : Series K) :
    letI := equationLocalRing K f hf
    nativeJetEquiv K f hf n (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a) := rfl

variable (L : Type v) [Field L] [Algebra K L]

local instance truncatedEquationCommRing (f : Series K) (n : ℕ) :
    CommRing (TruncatedEquation K f n) := inferInstance

local instance truncatedEquationAlgebra (f : Series K) (n : ℕ) :
    Algebra K (TruncatedEquation K f n) := inferInstance

/-- The whole equation ideal, not just its displayed generator, follows the actual finite coefficient map. -/
theorem equationJetIdeal_scalar_image (f : Series K) (n : ℕ) :
    ((equationJetIdeal K f n).map
      (Algebra.TensorProduct.includeRight.toRingHom : Jet K n →+* L ⊗[K] Jet K n)).map
        (scalarEquiv K L n).toRingHom =
      equationJetIdeal L (MvPowerSeries.map (algebraMap K L) f) n := by
  simp only [equationJetIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  change {scalarEquiv K L n ((1 : L) ⊗ₜ[K] Ideal.Quotient.mk _ f)} =
    {Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) f)}
  rw [scalarEquiv_tmul_mk, one_smul]

/-- Genuine scalar extension AFTER quotienting the actual finite ambient jet by the entire equation ideal. -/
def truncatedScalarEquiv (f : Series K) (n : ℕ) :
    (L ⊗[K] TruncatedEquation K f n) ≃ₐ[L]
      TruncatedEquation L (MvPowerSeries.map (algebraMap K L) f) n :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (Jet K n) L
    (equationJetIdeal K f n)).trans
    (Ideal.quotientEquivAlg _ _ (scalarEquiv K L n)
      (equationJetIdeal_scalar_image K L f n).symm)

/-- EVERY finite equation-jet pure tensor keeps the literal original coefficientwise image. -/
theorem truncatedScalarEquiv_tmul_mk (f : Series K) (n : ℕ) (l : L) (a : Series K) :
    truncatedScalarEquiv K L f n
      (l ⊗ₜ[K] Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _
        (l • Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) a)) := by
  change Ideal.Quotient.mk _ (scalarEquiv K L n (l ⊗ₜ[K] Ideal.Quotient.mk _ a)) = _
  rw [scalarEquiv_tmul_mk]

/-- The coefficient image equation has actual zero constant, internally. -/
theorem mapped_constantCoeff (f : Series K) (hf : constantCoeff f = 0) :
    constantCoeff (MvPowerSeries.map (algebraMap K L) f) = 0 := by
  rw [constantCoeff_map, hf, map_zero]

/-- Actual native maximal-power jets commute with coefficient extension at EVERY order, including zero. -/
def equationJetScalarEquiv (f : Series K) (hf : constantCoeff f = 0) (n : ℕ) :
    letI := equationLocalRing K f hf
    letI := equationLocalRing L (MvPowerSeries.map (algebraMap K L) f)
      (mapped_constantCoeff K L f hf)
    (L ⊗[K] (Equation f ⧸ maximalIdeal (Equation f) ^ n)) ≃ₐ[L]
      (Equation (MvPowerSeries.map (algebraMap K L) f) ⧸
        maximalIdeal (Equation (MvPowerSeries.map (algebraMap K L) f)) ^ n) := by
  let := equationLocalRing K f hf
  let := equationLocalRing L (MvPowerSeries.map (algebraMap K L) f)
    (mapped_constantCoeff K L f hf)
  exact ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (nativeJetEquiv K f hf n)).trans (truncatedScalarEquiv K L f n)).trans
    (nativeJetEquiv L (MvPowerSeries.map (algebraMap K L) f)
      (mapped_constantCoeff K L f hf) n).symm

/-- EVERY original representative and tensor coefficient follows the SAME actual native jet equivalence. -/
theorem equationJetScalarEquiv_tmul_mk (f : Series K) (hf : constantCoeff f = 0)
    (n : ℕ) (l : L) (a : Series K) :
    letI := equationLocalRing K f hf
    letI := equationLocalRing L (MvPowerSeries.map (algebraMap K L) f)
      (mapped_constantCoeff K L f hf)
    equationJetScalarEquiv K L f hf n
      (l ⊗ₜ[K] Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      l • Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) a)) := by
  let := equationLocalRing K f hf
  let := equationLocalRing L (MvPowerSeries.map (algebraMap K L) f)
    (mapped_constantCoeff K L f hf)
  change (nativeJetEquiv L (MvPowerSeries.map (algebraMap K L) f) (mapped_constantCoeff K L f hf) n).symm
    (truncatedScalarEquiv K L f n
      (l ⊗ₜ[K] nativeJetEquiv K f hf n (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)))) = _
  rw [nativeJetEquiv_mk, truncatedScalarEquiv_tmul_mk]
  apply (nativeJetEquiv L (MvPowerSeries.map (algebraMap K L) f) (mapped_constantCoeff K L f hf) n).injective
  rw [AlgEquiv.apply_symm_apply]
  change (Ideal.Quotient.mkₐ L
    (equationJetIdeal L (MvPowerSeries.map (algebraMap K L) f) n)).toLinearMap
      (l • Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) a)) =
    (nativeJetEquiv L (MvPowerSeries.map (algebraMap K L) f)
      (mapped_constantCoeff K L f hf) n).toLinearEquiv
      (l • Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) a)))
  rw [(Ideal.Quotient.mkₐ L _).toLinearMap.map_smul,
    (nativeJetEquiv L (MvPowerSeries.map (algebraMap K L) f)
      (mapped_constantCoeff K L f hf) n).toLinearEquiv.map_smul]
  rfl

end DeJongAlterations.Algebra.NodeFieldSeriesJetEquation
