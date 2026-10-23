import DeJongAlterations.Algebra.NodeFieldSeriesJetFrame
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-! Actual coefficient extension of the finite native series jets, at EVERY order. -/

noncomputable section

open MvPowerSeries TensorProduct

namespace DeJongAlterations.Algebra.NodeFieldSeriesJetScalar

open NodeFormalMorse NodeVariableMorse NodeFieldSeriesJetFrame

universe u v
variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The original coefficient map sends every entire variable power into the actual target power. -/
theorem map_variablePower_le (n : ℕ) :
    variableIdeal K ^ n ≤ (variableIdeal L ^ n).comap
      (MvPowerSeries.map (algebraMap K L)) := by
  intro f hf
  apply (mem_variableIdeal_pow_iff_order n _).mpr
  apply nat_le_order
  intro d hd
  rw [coeff_map]
  have hz := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd)
    ((mem_variableIdeal_pow_iff_order n _).mp hf))
  rw [hz, map_zero]

/-- The literal map on the SAME finite quotients, induced coefficientwise. -/
def coefficientJetMap (n : ℕ) : Jet K n →ₐ[K] Jet L n :=
  Ideal.quotientMapₐ _ (MvPowerSeries.mapAlgHom (Algebra.ofId K L))
    (map_variablePower_le K L n)

theorem coefficientJetMap_mk (n : ℕ) (f : Series K) :
    coefficientJetMap K L n (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) f) := rfl

/-- The actual finite-jet scalar map, defined before proving bijectivity. -/
def scalarMap (n : ℕ) : (L ⊗[K] Jet K n) →ₐ[L] Jet L n :=
  AlgHom.liftEquiv K L (Jet K n) (Jet L n) (coefficientJetMap K L n)

/-- EVERY pure tensor of an original series has its genuine coefficientwise image. -/
theorem scalarMap_tmul_mk (n : ℕ) (l : L) (f : Series K) :
    scalarMap K L n (l ⊗ₜ[K] Ideal.Quotient.mk _ f) =
      l • Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) f) := rfl

/-- The actual finite monomial expansion proves surjectivity, including order zero. -/
theorem scalarMap_surjective (n : ℕ) : Function.Surjective (scalarMap K L n) := by
  intro z
  obtain ⟨c, rfl⟩ := (toJet_bijective L n).surjective z
  refine ⟨∑ d : JetIndex n,
    c d ⊗ₜ[K] (Ideal.Quotient.mk _ (monomial d.val (1 : K))), ?_⟩
  rw [map_sum]
  change _ = Ideal.Quotient.mk _ (∑ d : JetIndex n, monomial d.val (c d))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [scalarMap_tmul_mk, map_monomial, map_one]
  change c d • (Ideal.Quotient.mkₐ L (variableIdeal L ^ n)).toLinearMap (monomial d.val 1) =
    (Ideal.Quotient.mkₐ L (variableIdeal L ^ n)).toLinearMap (monomial d.val (c d))
  rw [← (Ideal.Quotient.mkₐ L (variableIdeal L ^ n)).toLinearMap.map_smul]
  congr 1
  simpa only [smul_eq_mul, mul_one] using
    ((monomial d.val : L →ₗ[L] Series L).map_smul (c d) (1 : L)).symm

/-- Actual finite ranks prove injectivity of this SAME coefficient-induced map. -/
theorem scalarMap_bijective (n : ℕ) : Function.Bijective (scalarMap K L n) := by
  have hdim : Module.finrank L (L ⊗[K] Jet K n) = Module.finrank L (Jet L n) := by
    rw [Module.finrank_baseChange, jet_finrank K n, jet_finrank L n]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (scalarMap K L n).toLinearMap) hdim).mpr (scalarMap_surjective K L n),
    scalarMap_surjective K L n⟩

/-- Genuine scalar extension of EVERY finite native series jet; no entire-series tensor is used. -/
def scalarEquiv (n : ℕ) : (L ⊗[K] Jet K n) ≃ₐ[L] Jet L n :=
  AlgEquiv.ofBijective (scalarMap K L n) (scalarMap_bijective K L n)

theorem scalarEquiv_tmul_mk (n : ℕ) (l : L) (f : Series K) :
    scalarEquiv K L n (l ⊗ₜ[K] Ideal.Quotient.mk _ f) =
      l • Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) f) := rfl

theorem scalarEquiv_tmul_X (n : ℕ) (i : Fin 2) :
    scalarEquiv K L n ((1 : L) ⊗ₜ[K] Ideal.Quotient.mk _ (MvPowerSeries.X i)) =
      Ideal.Quotient.mk _ (MvPowerSeries.X i : Series L) := by
  rw [scalarEquiv_tmul_mk, map_X, one_smul]

theorem scalarEquiv_tmul_C (n : ℕ) (a : K) :
    scalarEquiv K L n ((1 : L) ⊗ₜ[K] Ideal.Quotient.mk _ (MvPowerSeries.C a)) =
      Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap K L a) : Series L) := by
  rw [scalarEquiv_tmul_mk, map_C, one_smul]

end DeJongAlterations.Algebra.NodeFieldSeriesJetScalar
