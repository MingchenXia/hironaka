import DeJongAlterations.Algebra.NodeVariableMorseJet
import DeJongAlterations.Algebra.NodeSingularDerivative
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The actual original formal Jacobian ideal of a nondegenerate quadratic jet

This computes native formal derivatives of the original equation itself.
It does not identify them with the original geometric coherent Fitting ideal.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K]

/-- Actual derivations lower powers of the original variable ideal by at most one. -/
theorem derivation_mem_pow (D : Derivation K (Series K) (Series K)) (n : ℕ)
    {f : Series K} (hf : f ∈ variableIdeal K ^ (n + 1)) : D f ∈ variableIdeal K ^ n := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun r hr s hs => ?_) (fun x y hx hy => ?_)
    · rw [D.leibniz]
      simp only [smul_eq_mul]
      apply Ideal.add_mem
      · exact Ideal.mul_mem_right _ _ hr
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hs (ih hr)
    · rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- The original variable ideal has its actual original two generators. -/
theorem variableIdeal_eq_pair : variableIdeal K = Ideal.span {(X 0 : Series K), X 1} := by
  unfold variableIdeal
  congr 1
  ext f
  simp [Fin.exists_fin_two, eq_comm]

/-- The actual original variable ideal lies in the original local maximal ideal. -/
theorem variableIdeal_le_maximalIdeal :
    variableIdeal K ≤ IsLocalRing.maximalIdeal (Series K) := by
  intro f hf
  have hc := constantCoeff_zero_of_mem_pow (by decide : 1 ≤ 1)
    (show f ∈ variableIdeal K ^ 1 by simpa only [pow_one] using hf)
  intro hu
  have hh := MvPowerSeries.isUnit_iff_constantCoeff.mp hu
  rw [hc] at hh
  exact not_isUnit_zero hh

/-- The native partial derivatives of the original cubic residual have actual quadratic order. -/
theorem pderiv_sub_jet_mem_pow (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) (i : Fin 2) :
    MvPowerSeries.pderiv K i f - MvPowerSeries.pderiv K i (jetQuadratic f hΔ).series ∈
      variableIdeal K ^ 2 := by
  rw [← map_sub, jetQuadratic_series]
  exact derivation_mem_pow (MvPowerSeries.pderiv K i) 2 (sub_quadraticJet_mem_pow f hc h0 h1)

/-- The actual original formal derivative ideal. -/
def originalJacobianIdeal (f : Series K) : Ideal (Series K) :=
  Ideal.span {MvPowerSeries.pderiv K (0 : Fin 2) f, MvPowerSeries.pderiv K (1 : Fin 2) f}

/-- Nondegeneracy of the original actual quadratic jet forces the whole original formal Jacobian ideal. -/
theorem originalJacobianIdeal_eq_variableIdeal (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) : originalJacobianIdeal f = variableIdeal K := by
  let Q := jetQuadratic f hΔ
  let J := originalJacobianIdeal f
  let I := variableIdeal K
  have hQ : Ideal.span {MvPowerSeries.pderiv K (0 : Fin 2) Q.series,
      MvPowerSeries.pderiv K (1 : Fin 2) Q.series} = I := by
    have hh := (NodeSingular.partialDerivativeIdeal_eq Q 0).trans variableIdeal_eq_pair.symm
    simpa only [map_zero, sub_zero] using hh
  have hq0 : MvPowerSeries.pderiv K (0 : Fin 2) Q.series ∈ I := by
    rw [← hQ]
    exact Ideal.subset_span (by simp)
  have hq1 : MvPowerSeries.pderiv K (1 : Fin 2) Q.series ∈ I := by
    rw [← hQ]
    exact Ideal.subset_span (by simp)
  have hd0 := pderiv_sub_jet_mem_pow f hc h0 h1 hΔ 0
  have hd1 := pderiv_sub_jet_mem_pow f hc h0 h1 hΔ 1
  have hJle : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro z (rfl | rfl)
    · have he : MvPowerSeries.pderiv K (0 : Fin 2) f =
          (MvPowerSeries.pderiv K 0 f - MvPowerSeries.pderiv K 0 Q.series) +
            MvPowerSeries.pderiv K 0 Q.series := by abel
      rw [he]
      exact Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero hd0) hq0
    · have he : MvPowerSeries.pderiv K (1 : Fin 2) f =
          (MvPowerSeries.pderiv K 1 f - MvPowerSeries.pderiv K 1 Q.series) +
            MvPowerSeries.pderiv K 1 Q.series := by abel
      rw [he]
      exact Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero hd1) hq1
  have hIle : I ≤ J ⊔ I ^ 2 := by
    conv_lhs => rw [← hQ]
    apply Ideal.span_le.mpr
    rintro z (rfl | rfl)
    · have he : MvPowerSeries.pderiv K (0 : Fin 2) Q.series = MvPowerSeries.pderiv K 0 f -
          (MvPowerSeries.pderiv K 0 f - MvPowerSeries.pderiv K 0 Q.series) := by abel
      rw [he]
      exact Ideal.sub_mem _ ((show J ≤ J ⊔ I ^ 2 from le_sup_left) (Ideal.subset_span (by simp)))
        ((show I ^ 2 ≤ J ⊔ I ^ 2 from le_sup_right) hd0)
    · have he : MvPowerSeries.pderiv K (1 : Fin 2) Q.series = MvPowerSeries.pderiv K 1 f -
          (MvPowerSeries.pderiv K 1 f - MvPowerSeries.pderiv K 1 Q.series) := by abel
      rw [he]
      exact Ideal.sub_mem _ ((show J ≤ J ⊔ I ^ 2 from le_sup_left) (Ideal.subset_span (by simp)))
        ((show I ^ 2 ≤ J ⊔ I ^ 2 from le_sup_right) hd1)
  have hle : I ≤ J := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I)
      (variableIdeal_le_maximalIdeal.trans (IsLocalRing.maximalIdeal_le_jacobson _))
    simpa only [Ideal.smul_eq_mul, pow_two] using hIle
  exact le_antisymm hJle hle

/-- The original constant-coefficient algebra map. -/
def seriesConstantMap : Series K →ₐ[K] K where
  __ := constantCoeff
  commutes' r := by simp [MvPowerSeries.algebraMap_apply]

/-- Its whole original kernel is exactly the original variable ideal. -/
theorem seriesConstantMap_kernel :
    RingHom.ker (seriesConstantMap (K := K)).toRingHom = variableIdeal K := by
  apply le_antisymm
  · intro f hf
    exact mem_variableIdeal_of_constantCoeff_eq_zero hf
  · apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    change constantCoeff (X i : Series K) = 0
    simp

/-- The literal original equation quotient. -/
abbrev Equation (f : Series K) := Series K ⧸ Ideal.span {f}

/-- The original formal derivative images in the actual original hypersurface. -/
def equationDerivativeIdeal (f : Series K) : Ideal (Equation f) :=
  (originalJacobianIdeal f).map (Ideal.Quotient.mk (Ideal.span {f}))

/-- The original vanishing constant internally supplies the original quotient evaluation. -/
def equationConstantMap (f : Series K) (hc : constantCoeff f = 0) : Equation f →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ seriesConstantMap (by
    change Ideal.span {f} ≤ RingHom.ker (seriesConstantMap (K := K)).toRingHom
    apply Ideal.span_le.mpr
    rintro g rfl
    exact hc)

/-- Every original field element is a value of the actual original constant evaluation. -/
theorem equationConstantMap_surjective (f : Series K) (hc : constantCoeff f = 0) :
    Function.Surjective (equationConstantMap f hc) := by
  intro a
  exact ⟨Ideal.Quotient.mk (Ideal.span {f}) (C a), by change constantCoeff (C a : Series K) = a; simp⟩

/-- The actual full original derivative-image ideal is the actual constant evaluation kernel. -/
theorem equationConstantMap_kernel (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) :
    RingHom.ker (equationConstantMap f hc).toRingHom = equationDerivativeIdeal f := by
  change RingHom.ker (Ideal.Quotient.lift (Ideal.span {f})
    (seriesConstantMap (K := K)).toRingHom _) =
      (originalJacobianIdeal f).map (Ideal.Quotient.mk (Ideal.span {f}))
  rw [Ideal.ker_quotient_lift, seriesConstantMap_kernel,
    originalJacobianIdeal_eq_variableIdeal f hc h0 h1 hΔ]

/-- The actual original formal hypersurface derivative quotient is the original field itself. -/
def equationJacobianQuotientEquiv (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) :
    (Equation f ⧸ equationDerivativeIdeal f) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (equationConstantMap_kernel f hc h0 h1 hΔ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (equationConstantMap_surjective f hc))

@[simp]
theorem equationJacobianQuotientEquiv_coefficient (f : Series K) (hc : constantCoeff f = 0)
    (h0 : coeff (Finsupp.single 0 1) f = 0) (h1 : coeff (Finsupp.single 1 1) f = 0)
    (hΔ : jetDiscriminant f ≠ 0) (r : K) :
    equationJacobianQuotientEquiv f hc h0 h1 hΔ
      (Ideal.Quotient.mk (equationDerivativeIdeal f) (Ideal.Quotient.mk (Ideal.span {f}) (C r))) = r :=
  rfl

end DeJongAlterations.Algebra.NodeVariableMorse
