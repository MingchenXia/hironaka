import DeJongAlterations.Algebra.NodeFieldSeriesJetEquation
import DeJongAlterations.Algebra.NodeVariableMorseSplitQuadratic
import DeJongAlterations.Algebra.NodeFieldJetDimensionDescent

/-! Genuine finite scalar-extension jets of the SAME original nondegenerate quadratic. -/

noncomputable section

open MvPowerSeries TensorProduct IsLocalRing

namespace DeJongAlterations.Algebra.NodeFieldSeriesJetQuadratic

open NodeFormalMorse NodeVariableMorse NodeFieldSeriesJetEquation NodeFieldQuadraticSource
  NodeGeometricCompletionFormalUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u v
variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] [IsAlgClosed L]

/-- The literal uv quotient and the SAME accepted native FormalUV have identical original series classes. -/
def literalUVEquiv : Equation ((X 0 : Series L) * X 1) ≃ₐ[L] FormalUV L :=
  Ideal.quotientEquivAlgOfEq L (by
    simp only [uvPolynomial, MvPolynomial.coe_mul, MvPolynomial.coe_X])

/-- The actual same-quadratic coordinate equivalence after the prescribed coefficient embedding. -/
def splitEquationEquiv (g : Series K) (hΔ : jetDiscriminant g ≠ 0) :
    Equation (MvPowerSeries.map (algebraMap K L) (quadraticJet g)) ≃ₐ[L] FormalUV L :=
  Ideal.quotientEquivAlg _ _
    (extendedQuadraticSplitEquiv (algebraMap K L) (jetQuadratic g hΔ)) (by
      rw [Ideal.map_span, Set.image_singleton]
      apply congrArg Ideal.span
      apply congrArg Set.singleton
      change ((uvPolynomial L) : Series L) =
        extendedQuadraticSplitEquiv (algebraMap K L) (jetQuadratic g hΔ)
          (MvPowerSeries.map (algebraMap K L) (quadraticJet g))
      rw [← jetQuadratic_series g hΔ, extendedQuadraticSplitEquiv_quadratic]
      simp only [uvPolynomial, MvPolynomial.coe_mul, MvPolynomial.coe_X])

/-- The actual original coordinate substitution on EVERY original series representative. -/
theorem splitEquationEquiv_mk (g : Series K) (hΔ : jetDiscriminant g ≠ 0) (a : Series L) :
    splitEquationEquiv K L g hΔ (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (extendedQuadraticSplitEquiv (algebraMap K L) (jetQuadratic g hΔ) a) := rfl

/-- The native maximal-power quotient of the actual split coordinate equivalence. -/
def splitJetEquiv (g : Series K) (hΔ : jetDiscriminant g ≠ 0) (n : ℕ) :
    letI := equationLocalRing L (MvPowerSeries.map (algebraMap K L) (quadraticJet g))
      (mapped_constantCoeff K L _ (quadraticJet_constantCoeff K g))
    (Equation (MvPowerSeries.map (algebraMap K L) (quadraticJet g)) ⧸
      maximalIdeal (Equation (MvPowerSeries.map (algebraMap K L) (quadraticJet g))) ^ n)
      ≃ₐ[L] (FormalUV L ⧸ maximalIdeal (FormalUV L) ^ n) := by
  let := equationLocalRing L (MvPowerSeries.map (algebraMap K L) (quadraticJet g))
    (mapped_constantCoeff K L _ (quadraticJet_constantCoeff K g))
  exact Ideal.quotientEquivAlg _ _ (splitEquationEquiv K L g hΔ) (by
    rw [Ideal.map_pow]
    exact (congrArg (fun I => I ^ n)
      (map_ringEquiv_maximalIdeal (splitEquationEquiv K L g hΔ).toRingEquiv)).symm)

/-- Actual scalar extension of EVERY native original quadratic-source jet to the SAME split node jet. -/
def quadraticNodeJetEquiv (g : Series K) (hΔ : jetDiscriminant g ≠ 0) (n : ℕ) :
    (L ⊗[K] (QuadraticSource K g ⧸ maximalIdeal (QuadraticSource K g) ^ n)) ≃ₐ[L]
      (FormalUV L ⧸ maximalIdeal (FormalUV L) ^ n) :=
  (equationJetScalarEquiv K L (quadraticJet g) (quadraticJet_constantCoeff K g) n).trans
    (splitJetEquiv K L g hΔ n)

/-- Every original series follows its actual coefficient extension and the SAME splitting substitution. -/
theorem quadraticNodeJetEquiv_tmul_mk (g : Series K) (hΔ : jetDiscriminant g ≠ 0)
    (n : ℕ) (l : L) (a : Series K) :
    quadraticNodeJetEquiv K L g hΔ n (l ⊗ₜ[K] Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      l • Ideal.Quotient.mk _ (Ideal.Quotient.mk _
        (extendedQuadraticSplitEquiv (algebraMap K L) (jetQuadratic g hΔ)
          (MvPowerSeries.map (algebraMap K L) a))) := by
  let := equationLocalRing L (MvPowerSeries.map (algebraMap K L) (quadraticJet g))
    (mapped_constantCoeff K L _ (quadraticJet_constantCoeff K g))
  change splitJetEquiv K L g hΔ n
    (equationJetScalarEquiv K L (quadraticJet g) (quadraticJet_constantCoeff K g) n
      (l ⊗ₜ[K] Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a))) = _
  rw [equationJetScalarEquiv_tmul_mk]
  let p : Equation (MvPowerSeries.map (algebraMap K L) (quadraticJet g)) ⧸
      maximalIdeal (Equation (MvPowerSeries.map (algebraMap K L) (quadraticJet g))) ^ n :=
    Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) a))
  have hs : splitJetEquiv K L g hΔ n (l • p) = l • splitJetEquiv K L g hΔ n p :=
    (splitJetEquiv K L g hΔ n).toLinearEquiv.map_smul l p
  exact hs

include L in
/-- Finiteness of the SAME native original quadratic jets descends faithfully flat from their actual split models. -/
theorem quadraticJet_finiteDimensional (g : Series K) (hΔ : jetDiscriminant g ≠ 0) (n : ℕ) :
    FiniteDimensional K (QuadraticSource K g ⧸ maximalIdeal (QuadraticSource K g) ^ n) :=
  NodeFieldJetDimensionDescent.originalJet_finiteDimensional K L (QuadraticSource K g) n
    (quadraticNodeJetEquiv K L g hΔ n).toLinearEquiv

include L in
/-- Every positive native original quadratic jet has its genuine node rank, with no rank input. -/
theorem quadraticJet_finrank_succ (g : Series K) (hΔ : jetDiscriminant g ≠ 0) (n : ℕ) :
    Module.finrank K (QuadraticSource K g ⧸ maximalIdeal (QuadraticSource K g) ^ (n + 1)) =
      2 * n + 1 :=
  NodeFieldJetDimensionDescent.originalJet_finrank_succ K L (QuadraticSource K g) n
    (quadraticNodeJetEquiv K L g hΔ (n + 1)).toLinearEquiv

end DeJongAlterations.Algebra.NodeFieldSeriesJetQuadratic
