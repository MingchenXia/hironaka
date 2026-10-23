import DeJongAlterations.Algebra.NodeFieldUVJetKernel
import DeJongAlterations.Algebra.NodeFieldFormalUVLocal
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Genuine finite monomial frames of the SAME original formal-node jets.
The finite monomial lift/coefficient proof adapts
TranscendentalNakamaye/Pending/HironakaActualFormalStandardMonomialHS.lean,
SHA256 aad17e550911eaaaa7216f2697a964c69a83350a7f10b225be9da34adc1ebdfb;
only Mathlib and accepted narrow local modules are imported. -/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldUVJetBasis

open NodeFormalMorse NodeFieldUVJetKernel NodeGeometricCompletionFormalUV
  NodeFieldFormalUVLocal

universe u
variable (K : Type u) [Field K]

abbrev AxisIndex (n : ℕ) :=
  {d : Fin 2 →₀ ℕ // d.degree < n ∧ (d 0 = 0 ∨ d 1 = 0)}

instance axisIndexFintype (n : ℕ) : Fintype (AxisIndex n) :=
  (Set.Finite.subset (Finsupp.finite_of_degree_lt (σ := Fin 2) n)
    (fun _ h => h.1)).fintype

/-- The literal finite sum of the actual original axis monomials. -/
def monomialLift (n : ℕ) : (AxisIndex n → K) →ₗ[K] Series K where
  toFun c := ∑ d : AxisIndex n, monomial d.val (c d)
  map_add' c e := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c e := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- EVERY indexed original exponent retains exactly its original scalar coefficient. -/
theorem monomialLift_coefficient (n : ℕ) (c : AxisIndex n → K) (d : AxisIndex n) :
    coeff d.val (monomialLift K n c) = c d := by
  change coeff d.val (∑ e : AxisIndex n, monomial e.val (c e)) = c d
  rw [map_sum, Finset.sum_eq_single_of_mem d (Finset.mem_univ d)]
  · exact coeff_monomial_same _ _
  · intro e _ hne
    have he : d.val ≠ e.val := fun h => hne (Subtype.ext h.symm)
    simp only [coeff_monomial, if_neg he]

/-- The actual finite monomial map into the ENTIRE original jet quotient. -/
def quotientMonomialMap (n : ℕ) :
    (AxisIndex n → K) →ₗ[K] (Series K ⧸ jetIdeal K n) :=
  (Ideal.Quotient.mkₐ K _).toLinearMap.comp (monomialLift K n)

/-- Actual axis coefficients prove BOTH whole-map bijectivity directions. -/
theorem quotientMonomialMap_bijective (n : ℕ) :
    Function.Bijective (quotientMonomialMap K n) := by
  constructor
  · intro c e hce
    have hz : quotientMonomialMap K n (c - e) = 0 := by rw [map_sub, hce, sub_self]
    have hm : monomialLift K n (c - e) ∈ jetIdeal K n :=
      Ideal.Quotient.eq_zero_iff_mem.mp hz
    funext d
    have hc := (mem_jetIdeal_iff n _).mp hm d.val d.property.1 d.property.2
    rw [monomialLift_coefficient] at hc
    exact sub_eq_zero.mp hc
  · intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    let c : AxisIndex n → K := fun d => coeff d.val f
    refine ⟨c, Ideal.Quotient.eq.mpr ?_⟩
    apply (mem_jetIdeal_iff n _).mpr
    intro d hdeg hd
    rw [map_sub, monomialLift_coefficient K n c ⟨d, hdeg, hd⟩]
    exact sub_self _

/-- A genuine linear equivalence, using the original field action on the WHOLE quotient. -/
def quotientMonomialEquiv (n : ℕ) :
    (AxisIndex n → K) ≃ₗ[K] (Series K ⧸ jetIdeal K n) :=
  LinearEquiv.ofBijective _ (quotientMonomialMap_bijective K n)

/-- Native third isomorphism theorem for the SAME actual original maximal-power quotient. -/
def nativeJetEquiv (n : ℕ) :
    (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ n) ≃ₐ[K] (Series K ⧸ jetIdeal K n) := by
  let I : Ideal (Series K) := Ideal.span {((uvPolynomial K) : Series K)}
  have hI : I = equationIdeal K := by
    simp only [I, equationIdeal, uvPolynomial, MvPolynomial.coe_mul, MvPolynomial.coe_X]
  exact ((Ideal.quotientEquivAlgOfEq K (maximalPower_eq_map_variables K n)).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ K I (NodeVariableMorse.variableIdeal K ^ n))).trans
    (Ideal.quotientEquivAlgOfEq K (congrArg (fun J => J ⊔ NodeVariableMorse.variableIdeal K ^ n) hI))

/-- EVERY original series representative has precisely its original class as image. -/
theorem nativeJetEquiv_mk (n : ℕ) (f : Series K) :
    nativeJetEquiv K n (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f)) =
      Ideal.Quotient.mk _ f := rfl

/-- The finite frame belongs to the ACTUAL native original maximal-power quotient. -/
def nativeJetLinearEquiv (n : ℕ) :
    (AxisIndex n → K) ≃ₗ[K] (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ n) :=
  (quotientMonomialEquiv K n).trans (nativeJetEquiv K n).symm.toLinearEquiv

instance nativeJet_finiteDimensional (n : ℕ) :
    FiniteDimensional K (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ n) :=
  Module.Finite.equiv (nativeJetLinearEquiv K n)

/-- The rank is computed from the actual finite monomial frame, not assumed. -/
theorem nativeJet_finrank (n : ℕ) :
    Module.finrank K (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ n) =
      Fintype.card (AxisIndex n) := by
  rw [← (nativeJetLinearEquiv K n).finrank_eq, Module.finrank_fintype_fun_eq_card]

end DeJongAlterations.Algebra.NodeFieldUVJetBasis
